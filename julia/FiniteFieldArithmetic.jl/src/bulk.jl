# Bulk and array operations (backlog J8): uniform sampling of arrays, multiplication by a fixed
# constant, matrix products, and bitsliced vectors. Theory and measurements: bulk.md beside this
# file. Broadcasting needs no code of its own: the element types are `isbits` numbers, so
# `a .* b`, `c .* a`, `inv.(a)` and fused expressions compile to plain loops over the scalar
# arithmetic (tested in test/bulk.jl).

# --- Random sampling --------------------------------------------------------------------------

# Arrays are filled with random bit patterns in one call on the storage type (which the RNG
# does in bulk, with SIMD for Xoshiro), then masked when the field does not fill its storage.
# Uniform: every bit pattern of the storage type is equally likely, and the mask keeps the low
# n bits. The elements differ from those of per-element sampling with the same seed.
function Random.rand!(rng::Random.AbstractRNG, A::Array{F},
                      ::Random.SamplerType{F}) where {F <: BinaryFieldElement}
    T = storagetype(F)
    if !storage_layout(F)                          # not a bare storage integer: element-wise
        for i in eachindex(A)
            @inbounds A[i] = rand(rng, F)
        end
        return A
    end
    try
        GC.@preserve A Random.rand!(rng, unsafe_wrap(Array, Ptr{T}(pointer(A)), size(A)))
    finally
        # Masked even when the RNG throws part-way: whatever it wrote stays a valid element.
        if !fills_storage(F)
            m = max_bits(F)
            @inbounds for i in eachindex(A)
                A[i] = unsafe_frombits(F, bits(A[i]) & m)
            end
        end
    end
    return A
end

# Whether an `F` is laid out exactly as its storage integer (a single field of that type), so an
# `Array{F}` may be filled through a pointer to `storagetype(F)`. Every representation in this
# package is; a subtype with another layout takes the element-wise path.
storage_layout(::Type{F}) where {F <: BinaryFieldElement} =
    isbitstype(F) && fieldcount(F) == 1 && fieldtype(F, 1) === storagetype(F) &&
    sizeof(F) == sizeof(storagetype(F))

# --- Multiplication by a constant -------------------------------------------------------------

"""
    MulBy(c::Nimber)

Multiplication by the constant `c`, prepared for many operands: `m = MulBy(c)`, then `m(x)`
equals `c * x`, and `m.(a)` multiplies an array. ``x \\mapsto c \\otimes x`` is linear over
``\\mathbb{F}_2``, so it is stored as byte tables: `m(x)` is one lookup per byte of `x` and XORs
(``n/8`` lookups in ``\\mathbb{F}_{2^n}``, one for ``n \\le 8``). Setting up costs ``n``
products and ``32 n`` XORs and ``32 n`` storage words (64 KiB at ``\\mathbb{F}_{2^{128}}``), so
it pays for long arrays only; the measurements are in `src/bulk.md`.
"""
struct MulBy{N <: Nimber, T <: Unsigned} <: Function
    c::N
    tab::Matrix{T}
    # The only constructor: the table is built here from `c`, never passed in, so it always has
    # 256 × sizeof(T) entries (`apply_bytes` reads it unchecked) and holds the products by `c`.
    function MulBy(c::N) where {K, T, N <: Nimber{K, T}}
        tab = Matrix{T}(undef, 256, sizeof(T))
        return new{N, T}(c, mulby_tables!(tab, c))
    end
end

# The byte tables of x ↦ c ⊗ x, written into `tab` (256 × sizeof(T)).
function mulby_tables!(tab::Matrix{T}, c::Nimber{K, T}) where {K, T}
    if K <= 3                                     # GF(256) and below: a column of the table
        @inbounds for b in 1:256
            tab[b, 1] = NIM256_MUL[b, Int(bits(c)) + 1] % T
        end
        return tab
    end
    s = default_strategy(typeof(c))
    img = ntuple(k -> nim_mul_bits(s, bits(c), one(T) << (k - 1), Val(K)), Val(8 * sizeof(T)))
    return byte_tables!(tab, img)
end
byte_tables!(tab::Matrix{T}, img::NTuple{M, T}) where {M, T <: Unsigned} =
    byte_tables!(tab, StaticImages(img))

# A read-only vector view of a tuple, so byte_tables! can take the images without allocating.
struct StaticImages{M, T} <: AbstractVector{T}
    v::NTuple{M, T}
end
Base.size(::StaticImages{M}) where {M} = (M,)
Base.@propagate_inbounds Base.getindex(s::StaticImages, i::Int) = s.v[i]

# (Callable structs are outside DispatchDoctor's reach; JET's @test_opt checks this one.)
@inline (m::MulBy{Nimber{K, T}, T})(x::Nimber{K, T}) where {K, T <: Unsigned} =
    unsafe_frombits(Nimber{K, T}, apply_bytes(m.tab, bits(x)))

# --- Constant times array in broadcasts (J8c, J8d) --------------------------------------------

# Operands of another type (elements of a lazy argument in a broadcast) get the scalar product.
@inline (m::MulBy)(x) = m.c * x

"""
    ConstMulStrategy

How a broadcast of a constant times an array (`c .* a`, `a .* c`, and `c * a`, which Base
computes by broadcasting) is computed, chosen per field by [`default_constmul_strategy`](@ref):

- [`ScalarConstMul`](@ref): the scalar `*`, element by element;
- [`LazyMulBy`](@ref): the byte tables of [`MulBy`](@ref) inside the fused broadcast, for long
  arrays.

Measurements and the choice of the defaults: `src/bulk.md`, "Constant times array".
"""
abstract type ConstMulStrategy end

"""
    ScalarConstMul()

`c .* a` multiplies element by element with the scalar `*`; fused expressions stay fused. Base's
behaviour; no field uses it by default any more (it was the default up to ``\\mathbb{F}_{256}``
until J8e, `src/bulk.md`).
"""
struct ScalarConstMul <: ConstMulStrategy end

"""
    LazyMulBy(threshold::Int)
    LazyMulBy(F) = LazyMulBy(mulby_threshold(F))

`c .* a` stays lazy and is decided when the (fused) broadcast is materialised: if the result has
at least `threshold` elements, every product with `c` is a lookup in the byte tables of
[`MulBy`](@ref)`(c)`, built once per broadcast; below, it is Base's broadcast of `*`
([`ScalarConstMul`](@ref)), so short arrays cost nothing extra. Fused expressions stay fused.
Implemented as a broadcast style (`ConstMulStyle`) that wraps the style of the arguments. The
default for every field, with the measured break-even [`mulby_threshold`](@ref).
"""
struct LazyMulBy <: ConstMulStrategy
    threshold::Int
end
LazyMulBy(::Type{N}) where {N <: Nimber} = LazyMulBy(mulby_threshold(N))

"""
    default_constmul_strategy(F)

The [`ConstMulStrategy`](@ref) behind `c .* a` and `a .* c` for a constant `c::F` and an array
(or lazy broadcast) `a`: [`LazyMulBy`](@ref)`(F)` for every field (`src/bulk.md`). To change it,
redefine it for a field, e.g.
`FiniteFieldArithmetic.default_constmul_strategy(::Type{GF2_64}) = ScalarConstMul()`.
"""
default_constmul_strategy(::Type{N}) where {N <: Nimber} = LazyMulBy(N)

"""
    mulby_threshold(F)

The array length from which [`LazyMulBy`](@ref) builds tables: the smallest measured length from
which it beat the scalar `*` in `c .* a`, `out .= c .* a` and `out .= c .* a .+ b`
(`bench/constmul.jl`; `src/bulk.md`, "Constant times array"): 96 at GF(2) … GF(256), 768 at
GF(2^16), 192 at GF(2^32), 256 at GF(2^64), 512 at GF(2^128).
"""
mulby_threshold(::Type{<:Nimber}) = 96
mulby_threshold(::Type{GF2_16}) = 768
mulby_threshold(::Type{GF2_32}) = 192
mulby_threshold(::Type{GF2_64}) = 256
mulby_threshold(::Type{GF2_128}) = 512

const ArrayOrLazy = Union{AbstractArray, Broadcast.Broadcasted}

"""
    const_mul_broadcasted(strategy::ConstMulStrategy, c, a)

What `Broadcast.broadcasted(*, c, a)` returns for a constant `c::Nimber` and an array or lazy
broadcast `a` under `strategy`: a lazy `Broadcasted`.
"""
const_mul_broadcasted(s::ConstMulStrategy, c::Nimber, a::ArrayOrLazy) =
    const_mul_broadcasted(s, c, a, (c, a))
const_mul_broadcasted(s::ConstMulStrategy, a::ArrayOrLazy, c::Nimber, args::Tuple) =
    const_mul_broadcasted(s, c, a, args)

# `args` is the argument tuple as written, (c, a) or (a, c); Base's broadcast keeps its order.
const_mul_broadcasted(::ScalarConstMul, ::Nimber, ::ArrayOrLazy, args::Tuple) =
    Broadcast.broadcasted(Broadcast.combine_styles(args...), *, args...)
const_mul_broadcasted(s::LazyMulBy, c::Nimber, a::ArrayOrLazy, args::Tuple) =
    Broadcast.Broadcasted{ConstMulStyle{typeof(Broadcast.combine_styles(args...))}}(
        ConstTimes(c, s.threshold), (a,))

# --- LazyMulBy as a broadcast style ---
#
# The decision between scalar products and tables must be one branch with two concrete call
# sites around the whole fused loop: a Union of two Broadcasted types returned by the hook (split
# by the compiler at materialize!) measured 1.74 ns per element at GF(2^16) fused, an explicit
# branch 1.50, Base's scalar loop 1.50 (src/bulk.md). The hook therefore returns a marker node,
# `ConstTimes`, in the style ConstMulStyle{S} (S: the style the arguments would have had). The
# style propagates to every enclosing node of the fused expression; `copyto!` and `copy` then
# compare the length of the result with the thresholds once and rewrite the tree to style S, with
# each marker replaced by Base's `*` broadcast or by a broadcast of MulBy(c).

# c ⊗ x, and the threshold of LazyMulBy. Callable, so an unrewritten tree is still correct.
struct ConstTimes{N <: Nimber} <: Function
    c::N
    threshold::Int
end
@inline (t::ConstTimes)(x) = t.c * x

struct ConstMulStyle{S <: Broadcast.BroadcastStyle} <: Broadcast.BroadcastStyle end

constmul_style(::Type{S}) where {S} = ConstMulStyle{S}()
Broadcast.BroadcastStyle(::ConstMulStyle{S}, o::Broadcast.BroadcastStyle) where {S} =
    constmul_style(typeof(Broadcast.result_style(S(), o)))
Broadcast.BroadcastStyle(o::Broadcast.BroadcastStyle, ::ConstMulStyle{S}) where {S} =
    constmul_style(typeof(Broadcast.result_style(o, S())))
Broadcast.BroadcastStyle(::ConstMulStyle{S}, ::ConstMulStyle{R}) where {S, R} =
    constmul_style(typeof(Broadcast.result_style(S(), R())))
# (Base's Unknown style would otherwise win against ours; keep ours, wrapping it.)
Broadcast.BroadcastStyle(::ConstMulStyle{S}, ::Broadcast.Unknown) where {S} = ConstMulStyle{S}()
Broadcast.BroadcastStyle(::Broadcast.Unknown, ::ConstMulStyle{S}) where {S} = ConstMulStyle{S}()

# The rewrite: Val(true) uses tables at every marker, Val(false) Base's `*`.
unwrap_constmul(x, ::Val) = x
unwrap_constmul(bc::Broadcast.Broadcasted{ConstMulStyle{S}}, v::Val) where {S} =
    Broadcast.Broadcasted{S}(unwrap_node(bc.f, unwrap_args(bc.args, v), v)..., bc.axes)
unwrap_args(args::Tuple, v::Val) = map(x -> unwrap_constmul(x, v), args)
# (function, arguments) of a rewritten node
unwrap_node(f, args::Tuple, ::Val) = (f, args)
unwrap_node(t::ConstTimes, args::Tuple, ::Val{true}) = (MulBy(t.c), args)
unwrap_node(t::ConstTimes, args::Tuple, ::Val{false}) = (*, (t.c, args...))

# The largest threshold of the markers in a tree (tables are used only if the result reaches it).
max_threshold(_) = 0
max_threshold(bc::Broadcast.Broadcasted) = max(node_threshold(bc.f), max_threshold_args(bc.args))
max_threshold_args(args::Tuple) = mapreduce(max_threshold, max, args; init = 0)
node_threshold(_) = 0
node_threshold(t::ConstTimes) = t.threshold

# Each branch behind a function barrier: with both loops inlined into one method, the fused loop
# at GF(2^16) ran at 1.63–1.65 ns per element against 1.47–1.49 for Base's (bench, src/bulk.md);
# with the barrier, equal from 1024 elements, about 9 ns more per call below. Cause: LLVM's loop
# unswitching budget shrinks with the number of loops in a method, so with both loops in one method
# a per-element index check of the broadcast stayed in the loop (bench/constmul_inline.jl).
@noinline unwrapped_copyto!(dest::AbstractArray, bc::Broadcast.Broadcasted, v::Val) =
    copyto!(dest, Broadcast.instantiate(unwrap_constmul(bc, v)))
@noinline unwrapped_copy(bc::Broadcast.Broadcasted, v::Val) =
    copy(Broadcast.instantiate(unwrap_constmul(bc, v)))

Base.copyto!(dest::AbstractArray, bc::Broadcast.Broadcasted{<:ConstMulStyle}) =
    length(dest) >= max_threshold(bc) ? unwrapped_copyto!(dest, bc, Val(true)) :
                                        unwrapped_copyto!(dest, bc, Val(false))
Base.copy(bc::Broadcast.Broadcasted{<:ConstMulStyle}) =
    length(bc) >= max_threshold(bc) ? unwrapped_copy(bc, Val(true)) : unwrapped_copy(bc, Val(false))

# The hooks. Only arrays whose element type is that of the constant, and lazy arguments (whose
# element type is not known here; MulBy falls back to `*` for other operands).
Broadcast.broadcasted(::typeof(*), c::N, a::AbstractArray{N}) where {N <: Nimber} =
    const_mul_broadcasted(default_constmul_strategy(N), c, a, (c, a))
Broadcast.broadcasted(::typeof(*), a::AbstractArray{N}, c::N) where {N <: Nimber} =
    const_mul_broadcasted(default_constmul_strategy(N), c, a, (a, c))
Broadcast.broadcasted(::typeof(*), c::N, a::Broadcast.Broadcasted) where {N <: Nimber} =
    const_mul_broadcasted(default_constmul_strategy(N), c, a, (c, a))
Broadcast.broadcasted(::typeof(*), a::Broadcast.Broadcasted, c::N) where {N <: Nimber} =
    const_mul_broadcasted(default_constmul_strategy(N), c, a, (a, c))

# --- Matrix products --------------------------------------------------------------------------

"""
    MatMulStrategy

How a matrix product over a nimber field is computed by [`matmul!`](@ref) (and hence by `*` and
`LinearAlgebra.mul!`, through [`default_matmul_strategy`](@ref)). All strategies give the same
result:

- [`ScalarMatMul`](@ref): the textbook loops with a scalar [`MulStrategy`](@ref).
- [`TableMatMul`](@ref): multiplication-by-constant tables ([`MulBy`](@ref)) per entry of `B`.
- [`CLMulMatMul`](@ref): carry-less products in the polynomial basis with one reduction per
  entry of the result.
- [`BitslicedMatMul`](@ref): ``n`` bit matrices and ``3^K`` products over ``\\mathbb{F}_2``.
- [`BySizeMatMul`](@ref): one of two strategies, chosen by the size of the product (the
  defaults).
"""
abstract type MatMulStrategy end

"""
    ScalarMatMul(strategy::MulStrategy)

The product ``C_{ij} = \\sum_k A_{ik} B_{kj}`` by the textbook loops (column by column, `B[k, j]`
times the column `A[:, k]`), each product with `strategy`.
"""
struct ScalarMatMul{S <: MulStrategy} <: MatMulStrategy
    strategy::S
end

"""
    TableMatMul()

The product column by column: ``C_{:,j} = \\sum_k A_{:,k} \\otimes B_{kj}``, each term through the
byte tables of multiplication by ``B_{kj}`` ([`MulBy`](@ref)), built once per entry of `B` into
a reused buffer and applied to the whole column of `A`. Up to ``\\mathbb{F}_{256}`` the table is
a column of the GF(256) product table and costs nothing to set up; above, the set-up (``n``
products) is paid per entry of `B` and only amortised over tall `A` (`src/bulk.md`).
"""
struct TableMatMul <: MatMulStrategy end

"""
    CLMulMatMul()

The product in the polynomial basis of [`CLMul`](@ref) (``\\mathbb{F}_{2^n}``, ``n \\ge 16``): both
matrices are converted once, every entry of the result is a sum of carry-less products, which is
reduced modulo ``f`` and converted back once (reduction is linear, so it commutes with the sum).
For a vector or two columns and a large `A` ([`clmul_by_columns`](@ref)) `A` is not converted
as a whole: it is read column by column in storage order and each entry converted on the fly,
with the unreduced sums kept per row of the result (FF-P2, `src/bulk.md`).
Needs `PCLMULQDQ` ([`has_pclmul`](@ref)); without it it computes as
`ScalarMatMul(MulTable())`, and up to ``\\mathbb{F}_{256}`` as [`TableMatMul`](@ref).
"""
struct CLMulMatMul <: MatMulStrategy end

# `default_matmul_strategy` is defined in bitsliced_matmul.jl (J8g: chosen by size).

"""
    matmul!(strategy::MatMulStrategy, C, A, B) -> C

Store the matrix product `A * B` in `C` (overwriting it), computed with `strategy`. `B` and `C`
may be vectors. `C` must not share memory with `A` or `B`.
"""
function matmul!(s::MatMulStrategy, C::StridedVecOrMat{N}, A::StridedMatrix{N},
                 B::StridedVecOrMat{N}) where {N <: Nimber}
    check_matmul(C, A, B)
    fill!(C, zero(N))
    return matmul_add!(s, C, A, B)
end

function check_matmul(C, A, B)
    m, p = size(A)
    (size(B, 1) == p && size(C, 1) == m && size(C, 2) == size(B, 2) && ndims(C) == ndims(B)) ||
        throw(DimensionMismatch("matmul!: C $(size(C)) ≠ A $(size(A)) × B $(size(B))"))
    (Base.mightalias(C, A) || Base.mightalias(C, B)) &&
        throw(ArgumentError("matmul!: output C must not share memory with A or B"))
    return nothing
end

@stable default_mode = "error" begin
    # C += A B, ScalarMatMul.
    function matmul_add!(sm::ScalarMatMul, C::StridedVecOrMat{N}, A::StridedMatrix{N},
                         B::StridedVecOrMat{N}) where {N <: Nimber}
        s = sm.strategy
        @inbounds for j in axes(B, 2), k in axes(A, 2)
            b = B[k, j]
            iszero(b) && continue
            for i in axes(A, 1)
                C[i, j] += mul(s, A[i, k], b)
            end
        end
        return C
    end

    # C += A B, TableMatMul.
    function matmul_add!(::TableMatMul, C::StridedVecOrMat{N}, A::StridedMatrix{N},
                         B::StridedVecOrMat{N}) where {K, T, N <: Nimber{K, T}}
        tab = Matrix{T}(undef, 256, sizeof(T))
        @inbounds for j in axes(B, 2), k in axes(A, 2)
            b = B[k, j]
            iszero(b) && continue
            mulby_tables!(tab, b)
            for i in axes(A, 1)
                C[i, j] += unsafe_frombits(N, apply_bytes(tab, bits(A[i, k])))
            end
        end
        return C
    end

    function matmul_add!(::CLMulMatMul, C::StridedVecOrMat{N}, A::StridedMatrix{N},
                         B::StridedVecOrMat{N}) where {K, T, N <: Nimber{K, T}}
        K <= 3 && return matmul_add!(TableMatMul(), C, A, B)
        has_pclmul() || return matmul_add!(ScalarMatMul(MulTable()), C, A, B)
        clmul_by_columns(N, size(A, 1), size(A, 2), size(B, 2)) &&
            return clmul_columns_add!(C, A, B)
        return clmul_transposed_add!(C, A, B)
    end

    # C += A B in the polynomial basis, A converted and transposed once, one `poly_dot` per entry
    # of C. The caller has checked `has_pclmul()` and K ≥ 4.
    function clmul_transposed_add!(C::StridedVecOrMat{N}, A::StridedMatrix{N},
                                   B::StridedVecOrMat{N}) where {K, T, N <: Nimber{K, T}}
        m, p = size(A)
        q = size(B, 2)
        At = Matrix{T}(undef, p, m)           # A transposed, so both factors run along k
        Bp = Matrix{T}(undef, p, q)
        @inbounds for i in 1:m, k in 1:p
            At[k, i] = to_poly(bits(A[i, k]))
        end
        @inbounds for j in 1:q, k in 1:p
            Bp[k, j] = to_poly(bits(B[k, j]))
        end
        @inbounds for j in 1:q, i in 1:m
            r = poly_dot(view(At, :, i), view(Bp, :, j))
            C[i, j] += unsafe_frombits(N, from_poly(r))
        end
        return C
    end

    # C += A B in the polynomial basis column by column (FF-P2): A is read in storage order and
    # each entry converted when it is used, the unreduced sums of products are kept per row and
    # reduced once per entry of C. Converts A once per column of B, so it pays for few columns
    # and a large A only (`clmul_by_columns`). The caller has checked `has_pclmul()` and K ≥ 4.
    function clmul_columns_add!(C::StridedVecOrMat{N}, A::StridedMatrix{N},
                                B::StridedVecOrMat{N}) where {K, T, N <: Nimber{K, T}}
        acc = Vector{poly_acc_type(T)}(undef, size(A, 1))
        @inbounds for j in axes(B, 2)
            fill!(acc, poly_acc_zero(T))
            for k in axes(A, 2)
                b = to_poly(bits(B[k, j]))
                iszero(b) && continue
                for i in axes(A, 1)
                    acc[i] = poly_mac(acc[i], to_poly(bits(A[i, k])), b)
                end
            end
            for i in axes(A, 1)
                C[i, j] += unsafe_frombits(N, from_poly(poly_acc_reduce(acc[i], T)))
            end
        end
        return C
    end
end

"""
    clmul_by_columns(F, m, p, q)

Whether [`CLMulMatMul`](@ref) computes the product of an `m × p` matrix `A` and a `p × q` matrix
(or vector, `q = 1`) column by column, converting each entry of `A` when it is used, rather than
converting and transposing `A` once. The column path saves the transpose, whose strided reads
cost most when `A` is large; it converts `A` once per column, so it pays for one or two columns
only. From `bench/matvec.jl sizes` (FF-P2, `src/bulk.md`, "Matrix × vector"): a vector when `A`
has at least 512 KiB; two columns when `A` has at least 4 MiB and `m, p ≥ 256`.
"""
function clmul_by_columns(::Type{F}, m::Integer, p::Integer, q::Integer) where {F <: Nimber}
    bytes = widemul(m, p) * sizeof(F)
    q == 1 && return bytes >= 512 * 1024
    q == 2 && return bytes >= 4 * 1024^2 && min(m, p) >= 256
    return false
end

# Unreduced sums of carry-less products, for clmul_columns_add!: the accumulator type of an
# n-bit field, its zero, a multiply-accumulate, and the reduction to n bits.
poly_acc_type(::Type{<:Union{UInt16, UInt32}}) = UInt64     # products of degree < 2n - 1 ≤ 63
poly_acc_type(::Type{UInt64}) = UInt128
poly_acc_type(::Type{UInt128}) = NTuple{3, UInt128}         # Karatsuba's three partial products
poly_acc_zero(::Type{<:Union{UInt16, UInt32}}) = zero(UInt64)
poly_acc_zero(::Type{UInt64}) = zero(UInt128)
poly_acc_zero(::Type{UInt128}) = (zero(UInt128), zero(UInt128), zero(UInt128))

@stable default_mode = "error" begin
    @inline poly_mac(acc::UInt64, a::T, b::T) where {T <: Union{UInt16, UInt32}} =
        acc ⊻ (clmul64_unchecked(a % UInt64, b % UInt64) % UInt64)
    @inline poly_mac(acc::UInt128, a::UInt64, b::UInt64) = acc ⊻ clmul64_unchecked(a, b)
    @inline function poly_mac(acc::NTuple{3, UInt128}, a::UInt128, b::UInt128)
        a1, a0 = (a >> 64) % UInt64, a % UInt64
        b1, b0 = (b >> 64) % UInt64, b % UInt64
        return (acc[1] ⊻ clmul64_unchecked(a0, b0), acc[2] ⊻ clmul64_unchecked(a1, b1),
                acc[3] ⊻ clmul64_unchecked(a0 ⊻ a1, b0 ⊻ b1))
    end
end

# The reduction of an accumulator to n bits. Outside `@stable` and one method per type: under
# `@stable` an argument `::Type{T}` with a free `T` was dispatched at runtime on every call (938 kB
# per 512 × 512 matrix × vector), and JET's package pass reads a free `T` as a union. JET checks
# these through `clmul_columns_add!`.
@inline poly_acc_reduce(acc::UInt64, ::Type{UInt16}) = poly_reduce((acc >> 16) % UInt16, acc % UInt16)
@inline poly_acc_reduce(acc::UInt64, ::Type{UInt32}) = poly_reduce((acc >> 32) % UInt32, acc % UInt32)
@inline poly_acc_reduce(acc::UInt128, ::Type{UInt64}) =
    poly_reduce((acc >> 64) % UInt64, acc % UInt64)
@inline function poly_acc_reduce(acc::NTuple{3, UInt128}, ::Type{UInt128})
    l, h, m = acc
    m ⊻= l ⊻ h
    return poly_reduce(h ⊻ (m >> 64), l ⊻ (m << 64))
end

# The carry-less product of the hardware when the caller has checked `has_pclmul()`; the branch
# of `clmul64` stays out of the inner loops.
@static if Sys.ARCH === :x86_64
    @inline clmul64_unchecked(a::UInt64, b::UInt64) = clmul64_hw(a, b)
else
    @inline clmul64_unchecked(a::UInt64, b::UInt64) = clmul64_sw(a, b)
end

@stable default_mode = "error" begin
    # Σ_k a_k b_k in F_2[x]/(f): the unreduced products are summed (XOR), then reduced once.
    @inline function poly_dot(a::AbstractVector{T}, b::AbstractVector{T}) where {T <: Union{UInt16, UInt32}}
        acc = zero(UInt64)                     # products have degree < 2n - 1 ≤ 63
        @inbounds for k in eachindex(a, b)
            acc ⊻= clmul64_unchecked(a[k] % UInt64, b[k] % UInt64) % UInt64
        end
        n = 8 * sizeof(T)
        return poly_reduce((acc >> n) % T, acc % T)
    end
    @inline function poly_dot(a::AbstractVector{UInt64}, b::AbstractVector{UInt64})
        acc = zero(UInt128)
        @inbounds for k in eachindex(a, b)
            acc ⊻= clmul64_unchecked(a[k], b[k])
        end
        return poly_reduce((acc >> 64) % UInt64, acc % UInt64)
    end
    # 128 bits: Karatsuba on 64-bit halves is linear in each product, so its three partial
    # products are summed separately and combined once.
    @inline function poly_dot(a::AbstractVector{UInt128}, b::AbstractVector{UInt128})
        l = h = m = zero(UInt128)
        @inbounds for k in eachindex(a, b)
            x, y = a[k], b[k]
            x1, x0 = (x >> 64) % UInt64, x % UInt64
            y1, y0 = (y >> 64) % UInt64, y % UInt64
            l ⊻= clmul64_unchecked(x0, y0)
            h ⊻= clmul64_unchecked(x1, y1)
            m ⊻= clmul64_unchecked(x0 ⊻ x1, y0 ⊻ y1)
        end
        m ⊻= l ⊻ h
        return poly_reduce(h ⊻ (m >> 64), l ⊻ (m << 64))
    end
end

# `*` and `mul!` for strided matrices and vectors over a nimber field: C = A B α + C β, with α, β
# Booleans or field elements (integers other than Booleans are not field elements here: an
# integer is a bit pattern, not the image of ℤ, see binaryfield.jl). Matrix–matrix and
# matrix–vector are separate methods, so that each is more specific than LinearAlgebra's.
const Scalar{N} = Union{Bool, N}

function LinearAlgebra.mul!(C::StridedMatrix{N}, A::StridedMatrix{N}, B::StridedMatrix{N},
                            α::Scalar{N}, β::Scalar{N}) where {N <: Nimber}
    return mul_add_scaled!(C, A, B, α, β)
end
function LinearAlgebra.mul!(C::StridedVector{N}, A::StridedMatrix{N}, B::StridedVector{N},
                            α::Scalar{N}, β::Scalar{N}) where {N <: Nimber}
    return mul_add_scaled!(C, A, B, α, β)
end

function mul_add_scaled!(C::StridedVecOrMat{N}, A, B, α, β) where {N <: Nimber}
    check_matmul(C, A, B)
    s = default_matmul_strategy(N)
    if iszero(β)
        fill!(C, zero(N))
    elseif !isone(β)
        C .*= β
    end
    iszero(α) && return C
    isone(α) && return matmul_add!(s, C, A, B)
    P = matmul!(s, similar(C), A, B)
    C .+= P .* α
    return C
end

# --- Bitsliced vectors ------------------------------------------------------------------------

# Four 64-bit words processed as one SIMD vector (256 bits; LLVM splits or merges it to the
# target's vector width). Only AND and XOR are needed.
const LANES = 4
const Vec4 = NTuple{LANES, VecElement{UInt64}}
struct Word4
    v::Vec4
end
for (f, op) in ((:⊻, "xor"), (:&, "and"))
    ir = "%r = $op <$LANES x i64> %0, %1\nret <$LANES x i64> %r"
    @eval @inline Base.$f(a::Word4, b::Word4) =
        Word4(Base.llvmcall($ir, Vec4, Tuple{Vec4, Vec4}, a.v, b.v))
end

"""
    BitslicedVector{N}(undef, n)
    BitslicedVector(a::AbstractVector{N})

A vector of ``n`` elements of the nimber field `N` stored
*bitsliced*: plane ``j`` holds bit ``j`` of every element, 64 elements per word. Element-wise
products are then a fixed circuit of AND and XOR on whole words (the recursion of
[`Recursive`](@ref), with ``\\mathbb{F}_2`` products as AND), run on four words at a time with
SIMD, so one circuit evaluation multiplies 256 pairs (at ``\\mathbb{F}_{2^{64}}`` and
``\\mathbb{F}_{2^{128}}`` the top one or two levels of the recursion run through memory, the
rest as at ``\\mathbb{F}_{2^{32}}``). Element-wise `.*` and `.+` of two
`BitslicedVector`s and [`mul_elementwise!`](@ref) use it; everything else (indexing, other
broadcasts) works element by element and is slow. Convert once with `BitslicedVector(a)` and back
with `Vector(v)`. Measurements in `src/bulk.md`.
"""
struct BitslicedVector{N <: Nimber} <: AbstractVector{N}
    planes::Matrix{UInt64}     # planes[w, j]: bit j - 1 of elements 64(w - 1) + 1 … 64w
    len::Int
    function BitslicedVector{N}(::UndefInitializer, n::Integer) where {N <: Nimber}
        nw = LANES * cld(cld(n, 64), LANES)    # whole SIMD words; the padding stays zero
        return new{N}(zeros(UInt64, nw, degree(N)), n)
    end
end

Base.size(v::BitslicedVector) = (v.len,)
Base.IndexStyle(::Type{<:BitslicedVector}) = IndexLinear()
Base.similar(v::BitslicedVector{N}) where {N} = BitslicedVector{N}(undef, length(v))

Base.@propagate_inbounds function Base.getindex(v::BitslicedVector{N}, i::Int) where {N}
    @boundscheck checkbounds(v, i)
    T = storagetype(N)
    w, t = ((i - 1) >> 6) + 1, (i - 1) & 63
    x = zero(T)
    @inbounds for j in 1:degree(N)
        x |= (((v.planes[w, j] >> t) & one(UInt64)) % T) << (j - 1)
    end
    return unsafe_frombits(N, x)
end

Base.@propagate_inbounds function Base.setindex!(v::BitslicedVector{N}, x, i::Int) where {N}
    @boundscheck checkbounds(v, i)
    b = bits(convert(N, x))
    w, t = ((i - 1) >> 6) + 1, (i - 1) & 63
    @inbounds for j in 1:degree(N)
        bit = UInt64((b >> (j - 1)) & one(b))
        v.planes[w, j] = (v.planes[w, j] & ~(one(UInt64) << t)) | (bit << t)
    end
    return v
end

function BitslicedVector(a::AbstractVector{N}) where {N <: Nimber}
    v = BitslicedVector{N}(undef, length(a))
    pack!(v.planes, a)
    return v
end

function Base.Vector{N}(v::BitslicedVector{N}) where {N}
    a = Vector{N}(undef, length(v))
    unpack!(a, v.planes)
    return a
end
Base.Vector(v::BitslicedVector{N}) where {N} = Vector{N}(v)
Base.collect(v::BitslicedVector{N}) where {N} = Vector{N}(v)

function Base.copyto!(dest::BitslicedVector{N}, src::BitslicedVector{N}) where {N}
    length(dest) == length(src) || throw(DimensionMismatch("copyto!: lengths differ"))
    copyto!(dest.planes, src.planes)
    return dest
end

# Element-wise operations on two bitsliced vectors stay bitsliced (`materialize` returns a
# non-`Broadcasted` value unchanged, so `a .* b` is this result).
# Operands of different lengths follow Julia's broadcasting rules: a length-1 operand is expanded
# (to a bitsliced vector of its one element repeated), any other mismatch is an error.
function Base.Broadcast.broadcasted(::typeof(*), a::BitslicedVector{N},
                                    b::BitslicedVector{N}) where {N}
    a, b = bs_expand(a, b)
    return mul_elementwise!(similar(a), a, b)
end
function Base.Broadcast.broadcasted(::typeof(+), a::BitslicedVector{N},
                                    b::BitslicedVector{N}) where {N}
    a, b = bs_expand(a, b)
    c = similar(a)
    c.planes .= a.planes .⊻ b.planes
    return c
end

function bs_expand(a::BitslicedVector{N}, b::BitslicedVector{N}) where {N}
    la, lb = length(a), length(b)
    la == lb && return a, b
    la == 1 && return BitslicedVector(fill(a[1], lb)), b
    lb == 1 && return a, BitslicedVector(fill(b[1], la))
    throw(DimensionMismatch("arrays could not be broadcast to a common size: lengths $la and $lb"))
end

"""
    mul_elementwise!(c, a, b) -> c

The element-wise product `c .= a .* b`. For [`BitslicedVector`](@ref)s it runs the bitsliced
circuit on the planes; for other arrays it is `broadcast!(*, c, a, b)`.
"""
mul_elementwise!(c::AbstractArray, a::AbstractArray, b::AbstractArray) = broadcast!(*, c, a, b)

@stable default_mode = "error" begin
    function mul_elementwise!(c::BitslicedVector{N}, a::BitslicedVector{N},
                              b::BitslicedVector{N}) where {N}
        length(a) == length(b) == length(c) ||
            throw(DimensionMismatch("lengths $(length(c)), $(length(a)), $(length(b))"))
        bitsliced_mul!(c.planes, a.planes, b.planes, Val(degree(N)))
        return c
    end
end

@inline load4(P::Matrix{UInt64}, w::Int, j::Int) =
    @inbounds Word4(ntuple(l -> VecElement(P[w + l - 1, j]), Val(LANES)))
@inline function store4!(P::Matrix{UInt64}, x::Word4, w::Int, j::Int)
    for l in 1:LANES
        @inbounds P[w + l - 1, j] = x.v[l].value
    end
    return nothing
end

function bitsliced_mul!(C::Matrix{UInt64}, A::Matrix{UInt64}, B::Matrix{UInt64},
                        ::Val{n}) where {n}
    for w in 1:LANES:size(A, 1)
        a = ntuple(j -> load4(A, w, j), Val(n))
        b = ntuple(j -> load4(B, w, j), Val(n))
        r = bs_mul(a, b)
        for j in 1:n
            store4!(C, r[j], w, j)
        end
    end
    return C
end

# GF(2^64) and GF(2^128) (J8b): the tuples of 64 or 128 vectors do not stay in registers (fully
# unrolled, a prototype took 28 and 158 ns per element). So the top one or two levels of the
# recursion run through a scratch buffer of `Word4`s, and every level-5 product is the unrolled
# GF(2^32) circuit on tuples of 32. Buffer layout of a level-L product at offset `to`:
# d (h words), c (h), a0 ⊻ a1 (h), b0 ⊻ b1 (h), then the scratch of level L - 1 (h = 2^(L-1)).
bitsliced_mul!(C::Matrix{UInt64}, A::Matrix{UInt64}, B::Matrix{UInt64}, v::Val{64}) =
    bitsliced_mul_mem!(C, A, B, v)
bitsliced_mul!(C::Matrix{UInt64}, A::Matrix{UInt64}, B::Matrix{UInt64}, v::Val{128}) =
    bitsliced_mul_mem!(C, A, B, v)
function bitsliced_mul_mem!(C::Matrix{UInt64}, A::Matrix{UInt64}, B::Matrix{UInt64},
                            ::Val{n}) where {n}
    L = Val(trailing_zeros(n))
    a, b, c = (Vector{Word4}(undef, n) for _ in 1:3)
    tmp = Vector{Word4}(undef, 3n)
    for w in 1:LANES:size(A, 1)
        for j in 1:n
            @inbounds a[j] = load4(A, w, j)
            @inbounds b[j] = load4(B, w, j)
        end
        bs_mul_mem!(c, 0, a, 0, b, 0, L, tmp, 0)
        for j in 1:n
            @inbounds store4!(C, c[j], w, j)
        end
    end
    return C
end

@inline load_words(x::Vector{Word4}, o::Int, ::Val{M}) where {M} =
    ntuple(i -> @inbounds(x[o + i]), Val(M))
@inline function store_words!(x::Vector{Word4}, o::Int, t::NTuple{M, Word4}) where {M}
    for i in 1:M
        @inbounds x[o + i] = t[i]
    end
    return nothing
end

# out[oo + 1 : oo + 2^L] = the product of a[ao + 1 : …] and b[bo + 1 : …] at level L.
@inline function bs_mul_mem!(out::Vector{Word4}, oo::Int, a::Vector{Word4}, ao::Int,
                             b::Vector{Word4}, bo::Int, ::Val{5}, ::Vector{Word4}, ::Int)
    store_words!(out, oo, bs_mul(load_words(a, ao, Val(32)), load_words(b, bo, Val(32))))
    return nothing
end
for L in (6, 7)
    @eval function bs_mul_mem!(out::Vector{Word4}, oo::Int, a::Vector{Word4}, ao::Int,
                               b::Vector{Word4}, bo::Int, ::Val{$L}, tmp::Vector{Word4}, to::Int)
        h = $(1 << (L - 1))
        sub = Val($(L - 1))
        bs_mul_mem!(tmp, to, a, ao, b, bo, sub, tmp, to + 4h)                  # d = a0 b0
        bs_mul_mem!(tmp, to + h, a, ao + h, b, bo + h, sub, tmp, to + 4h)      # c = a1 b1
        @inbounds for i in 1:h
            tmp[to + 2h + i] = a[ao + i] ⊻ a[ao + h + i]
            tmp[to + 3h + i] = b[bo + i] ⊻ b[bo + h + i]
        end
        bs_mul_mem!(out, oo + h, tmp, to + 2h, tmp, to + 3h, sub, tmp, to + 4h)  # e
        bs_half_mem!(out, oo, tmp, to + h, sub)                                 # half(c)
        @inbounds for i in 1:h
            d = tmp[to + i]
            out[oo + i] ⊻= d                                                    # d ⊕ half(c)
            out[oo + h + i] ⊻= d                                                # e ⊕ d
        end
        return nothing
    end
end
# out[oo + 1 : oo + 2^L] = half(c) at level L (out and c do not overlap).
@inline function bs_half_mem!(out::Vector{Word4}, oo::Int, c::Vector{Word4}, co::Int, ::Val{5})
    store_words!(out, oo, bs_half(load_words(c, co, Val(32))))
    return nothing
end
@inline function bs_half_mem!(out::Vector{Word4}, oo::Int, c::Vector{Word4}, co::Int, ::Val{6})
    c0, c1 = load_words(c, co, Val(32)), load_words(c, co + 32, Val(32))
    store_words!(out, oo, bs_half(bs_half(c1)))
    store_words!(out, oo + 32, bs_half(ntuple(i -> c0[i] ⊻ c1[i], Val(32))))   # not map: > 31
    return nothing
end

# The recursion of `Recursive` on planes: an element of level K is a tuple of 2^K planes (lowest
# bit first), its halves are the two halves of the tuple, ⊕ is XOR of planes, and the level-0
# product is AND. The tuples are fully unrolled, so the whole circuit is straight-line code.
# One method per tuple length (levels 1–5), so that every signature is concrete.
const Planes{M} = NTuple{M, Word4}

@inline bs_half(c::Planes{1}) = c
@inline bs_mul(a::Planes{1}, b::Planes{1}) = (a[1] & b[1],)
for M in (2, 4, 8, 16, 32)
    h = M ÷ 2
    @eval begin
        @inline lo_half(t::Planes{$M}) = ntuple(i -> t[i], Val($h))
        @inline hi_half(t::Planes{$M}) = ntuple(i -> t[$h + i], Val($h))
        @inline plane_xor(a::Planes{$h}, b::Planes{$h}) = map(⊻, a, b)
        @inline function bs_half(c::Planes{$M})                 # c ⊗ 2^(2^k - 1), see nimber.jl
            c0, c1 = lo_half(c), hi_half(c)
            return (bs_half(bs_half(c1))..., bs_half(plane_xor(c0, c1))...)
        end
        @inline function bs_mul(a::Planes{$M}, b::Planes{$M})
            a0, a1, b0, b1 = lo_half(a), hi_half(a), lo_half(b), hi_half(b)
            c = bs_mul(a1, b1)
            d = bs_mul(a0, b0)
            e = bs_mul(plane_xor(a0, a1), plane_xor(b0, b1))
            return (plane_xor(d, bs_half(c))..., plane_xor(e, d)...)
        end
    end
end

# Packing by bit-matrix transposes (J8b). A block of 64 elements of n bits is a 64 × n bit
# matrix (row t: element t, column j: its bit j); the n planes of the block are its transpose.
# The transpose of a 64 × 64 bit matrix is six delta swaps: the stage of distance j (32, 16, …, 1)
# exchanges bit log2(j) of the row index with the same bit of the column index, and the stages
# commute. With only n columns, the stages j ≥ n merely gather element t into word t mod n at bit
# offset n (t ÷ n); the stages j < n then run on those n words only. So a block costs one
# gather (one shift and OR per element) and n/2 · log2(n) swaps, instead of 64 n bit moves.
# Measurements in bulk.md, "Bitsliced vectors".

# The mask of the stage of distance j: the low j bits of every 2j-bit group.
delta_mask(j::Int) = ~zero(UInt64) ÷ ((one(UInt64) << j) + one(UInt64))

# The delta swap of distance j on a block of rows held in a tuple (j a power of two, j < n).
# Tuples rather than an array: with n and j constants, the block stays in registers and every
# stage unrolls (an array buffer measured 1.5-2.5 times slower at GF(2^16) and GF(2^32)).
@inline function delta_stage(x::NTuple{n, UInt64}, ::Val{j}) where {n, j}
    m = delta_mask(j)
    return ntuple(Val(n)) do i
        k = i - 1
        if k & j == 0
            @inbounds x[i] ⊻ ((((x[i] >> j) ⊻ x[i + j]) & m) << j)
        else
            @inbounds x[i] ⊻ ((((x[i - j] >> j) ⊻ x[i]) & m))
        end
    end
end

# The stages j = n/2, …, 1: the transpose of a gathered block of n rows.
@inline transpose_gathered(x::NTuple{1, UInt64}) = x
for n in (2, 4, 8, 16, 32, 64)
    body = :x
    j = n >> 1
    while j >= 1
        body = :(delta_stage($body, Val($j)))
        j >>= 1
    end
    @eval @inline transpose_gathered(x::NTuple{$n, UInt64}) = $body
end

"""
    transpose64!(x::AbstractVector{UInt64}) -> x

Transpose in place the 64 × 64 bit matrix whose row ``r`` is `x[r + 1]` (column ``c``: bit ``c``),
by six delta swaps. Used, restricted to ``n`` columns, to pack and unpack
[`BitslicedVector`](@ref)s.
"""
function transpose64!(x::AbstractVector{UInt64})
    length(x) == 64 || throw(DimensionMismatch("transpose64!: need 64 words, got $(length(x))"))
    y = transpose_gathered(ntuple(i -> @inbounds(x[firstindex(x) + i - 1]), Val(64)))
    copyto!(x, y)
    return x
end

function pack!(P::Matrix{UInt64}, a::AbstractVector{N}) where {N <: Nimber}
    return pack!(P, a, Val(degree(N)))
end
function pack!(P::Matrix{UInt64}, a::AbstractVector{N}, ::Val{n}) where {N <: Nimber, n}
    len = length(a)
    nfull = len >> 6
    for w in 1:nfull
        block_planes!(view(P, w, :), a, firstindex(a) + 64 * (w - 1), Val(n))
    end
    if len > 64 * nfull                              # the last block, padded with zeros
        tail = zeros(N, 64)
        copyto!(tail, 1, a, firstindex(a) + 64 * nfull, len - 64 * nfull)
        block_planes!(view(P, nfull + 1, :), tail, 1, Val(n))
    end
    return P
end

# y[1:n] = the n planes of the 64 elements a[first], …, a[first + 63]. GF(2^128): the two 64-bit
# halves of the elements are two 64 × 64 bit matrices, transposed separately (a tuple of 128
# words would leave registers and, past 32 elements, Base's tuple code allocates).
@inline function block_planes!(y::AbstractVector{UInt64}, a::AbstractVector, first::Int,
                               ::Val{n}) where {n}
    store_tuple!(y, 0, transpose_gathered(gather_block(a, first, Val(n), 0)))
    return y
end
@inline function block_planes!(y::AbstractVector{UInt64}, a::AbstractVector, first::Int,
                               ::Val{128})
    store_tuple!(y, 0, transpose_gathered(gather_block(a, first, Val(64), 0)))
    store_tuple!(y, 64, transpose_gathered(gather_block(a, first, Val(64), 64)))
    return y
end
@inline function store_tuple!(y::AbstractVector{UInt64}, o::Int, x::NTuple{n, UInt64}) where {n}
    for j in 1:n
        @inbounds y[firstindex(y) + o + j - 1] = x[j]
    end
    return y
end
@inline load_tuple(y::AbstractVector{UInt64}, o::Int, ::Val{n}) where {n} =
    ntuple(j -> @inbounds(y[firstindex(y) + o + j - 1]), Val(n))

# Row k + 1 = Σ_i element (n i + k) << (n i), of the element's bits from `shift` on: the stages
# j ≥ n of the transpose.
@inline function gather_block(a::AbstractVector{N}, first::Int, ::Val{n}, shift::Int) where {N, n}
    return ntuple(Val(n)) do r
        acc = zero(UInt64)
        for i in 0:(64 ÷ n - 1)
            acc |= ((bits(@inbounds a[first + n * i + r - 1]) >> shift) % UInt64) << (n * i)
        end
        acc
    end
end

function unpack!(a::AbstractVector{N}, P::Matrix{UInt64}) where {N <: Nimber}
    return unpack!(a, P, Val(degree(N)))
end
function unpack!(a::AbstractVector{N}, P::Matrix{UInt64}, ::Val{n}) where {N <: Nimber, n}
    len = length(a)
    nfull = len >> 6
    for w in 1:nfull
        block_from_planes!(a, firstindex(a) + 64 * (w - 1), view(P, w, :), Val(n))
    end
    if len > 64 * nfull
        tail = Vector{N}(undef, 64)
        block_from_planes!(tail, 1, view(P, nfull + 1, :), Val(n))
        copyto!(a, firstindex(a) + 64 * nfull, tail, 1, len - 64 * nfull)
    end
    return a
end

# The inverse of block_planes!: a[first], …, a[first + 63] from their n planes y[1:n].
@inline block_from_planes!(a::AbstractVector, first::Int, y::AbstractVector{UInt64},
                           ::Val{n}) where {n} =
    scatter_block!(a, transpose_gathered(load_tuple(y, 0, Val(n))), first)   # an involution
@inline function block_from_planes!(a::AbstractVector{N}, first::Int, y::AbstractVector{UInt64},
                                    ::Val{128}) where {N}
    lo = transpose_gathered(load_tuple(y, 0, Val(64)))
    hi = transpose_gathered(load_tuple(y, 64, Val(64)))
    for k in 0:63
        x = (UInt128(hi[k + 1]) << 64) | UInt128(lo[k + 1])
        @inbounds a[first + k] = unsafe_frombits(N, x % storagetype(N))
    end
    return a
end

# The inverse of gather_block.
@inline function scatter_block!(a::AbstractVector{N}, x::NTuple{n, UInt64}, first::Int) where {N, n}
    T = storagetype(N)
    m = n == 64 ? ~zero(UInt64) : (one(UInt64) << n) - one(UInt64)
    for i in 0:(64 ÷ n - 1), k in 0:(n - 1)
        @inbounds a[first + n * i + k] = unsafe_frombits(N, ((x[k + 1] >> (n * i)) & m) % T)
    end
    return a
end
