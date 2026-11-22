# J10: the rank-encoded fields GF(2^n) ⊂ Conway's On_2 for every n ≤ 128 (ADR-0005). For n = 2^k
# these are the nimbers (`Nimber`); for the other n, `Nim{n, T}`. The data (change of basis to an
# internal polynomial basis, inclusions) come from the research computation R1, src/nim_data.jl.
# Theory, design and measurements: nimfield.md beside this file.

include("nim_data.jl")

"""
    Nim{N, T<:Unsigned} <: BinaryFieldElement

An element of ``\\mathbb{F}_{2^N}`` for ``N \\le 128`` not a power of two, in the canonical
representation of ADR-0005: ``\\mathbb{F}_{2^N}`` is the subfield of Conway's field of nimbers
``\\mathbf{On}_2`` with ``2^N`` elements, and the element is stored as its **rank**: its position
(from 0) among those ``2^N`` ordinals in ordinal order. The rank is `F2`-linear, so addition is
XOR, and for ``N = 2^k`` it is the nimber value itself, which is why those fields are
[`Nimber`](@ref) and not `Nim`.

Get the type with [`nim_field`](@ref)`(n)`. Fields of different degree are related by the
inclusions of ``\\mathbf{On}_2`` ([`embed`](@ref)); elements compare equal (and hash equal) when
they are the same ordinal, and mixed arithmetic promotes to the field of degree
``\\operatorname{lcm}(m, n)`` when that is at most 128.
"""
struct Nim{N, T <: Unsigned} <: BinaryFieldElement
    bits::T
    function Nim{N, T}(b::T, ::Val{:unchecked}) where {N, T <: Unsigned}
        check_nim_params(N, T)
        return new{N, T}(b)
    end
end

@inline function check_nim_params(N, ::Type{T}) where {T}
    (N isa Int && 1 <= N <= 128 && !ispow2(N)) ||
        throw(ArgumentError("Nim{$N}: the degree must be an Int in 1:128, not a power of two (those are Nimber)"))
    poly_storage(N) === T || throw(ArgumentError("Nim{$N, $T}: GF(2^$N) is stored in $(poly_storage(N))"))
    return nothing
end

bits(x::Nim) = x.bits
storagetype(::Type{Nim{N, T}}) where {N, T} = T
degree(::Type{Nim{N, T}}) where {N, T} = N
unsafe_frombits(::Type{P}, b::T) where {N, T, P <: Nim{N, T}} = P(b, Val(:unchecked))

function Nim{N, T}(k::Integer) where {N, T <: Unsigned}
    P = Nim{N, T}
    check_nim_params(N, T)
    0 <= k <= max_bits(P) || throw(ArgumentError("$k is not a rank in GF(2^$N) (needs 0 ≤ k < 2^$N)"))
    return unsafe_frombits(P, k % T)
end

"""
    nim_field(n::Integer)
    nim_field(Val(n))

The field ``\\mathbb{F}_{2^n} \\subset \\mathbf{On}_2`` in the rank encoding (ADR-0005), for
``1 \\le n \\le 128``: the [`Nimber`](@ref) type of that degree when ``n = 2^k``, else
[`Nim`](@ref)`{n}`. `nim_field(Val(n))` is type-stable, `nim_field(n)` is not.

```jldoctest
julia> F = nim_field(3); F(2) * F(2)
0x4 ∈ GF(2^3)
```
"""
function nim_field end

nim_field(::Val{n}) where {n} = throw(ArgumentError("nim_field: n = $n is not in 1:128"))
for n in 1:128
    F = ispow2(n) ? Nimber{trailing_zeros(n), nimber_storage(trailing_zeros(n))} : Nim{n, poly_storage(n)}
    @eval nim_field(::Val{$n}) = $F
end
nim_field(n::Integer) = 1 <= n <= 128 ? nim_field(Val(Int(n))) :
    throw(ArgumentError("nim_field: n = $n is not in 1:128"))

# --- Data: change of basis and inclusions -------------------------------------------------------

hexcols(s::String, n::Int) = (w = cld(n, 4); [parse(UInt128, s[(i - 1) * w + 1:i * w]; base = 16) for i in 1:(length(s) ÷ w)])

# The inverse of an invertible n × n matrix over GF(2) given by its columns (UInt128 bit vectors).
function gf2_inverse(cols::Vector{UInt128}, n::Int)
    piv = Tuple{UInt128, UInt128}[]                  # (vector, combination of unit vectors)
    for i in 1:n
        r, c = cols[i], UInt128(1) << (i - 1)
        for (pr, pc) in piv
            if !iszero(r & (UInt128(1) << (127 - leading_zeros(pr))))
                r ⊻= pr; c ⊻= pc
            end
        end
        iszero(r) && error("gf2_inverse: singular matrix")
        push!(piv, (r, c))
        sort!(piv; by = x -> leading_zeros(x[1]))
    end
    return [gf2_solve(piv, UInt128(1) << (j - 1)) for j in 1:n]
end
function gf2_solve(piv, v::UInt128)
    c = zero(UInt128)
    for (pr, pc) in piv
        if !iszero(v & (UInt128(1) << (127 - leading_zeros(pr))))
            v ⊻= pr; c ⊻= pc
        end
    end
    iszero(v) || error("gf2_solve: not in the span")
    return c
end

padimg(::Type{T}, cols) where {T} = vcat(T[c % T for c in cols], zeros(T, 8 * sizeof(T) - length(cols)))

# Per field: byte tables rank → polynomial coordinates of g (`to`) and back (`from`), and the
# element 0 of the polynomial-basis field GF(2)[x]/(minpoly of g), all compile-time constants.
@generated function nim_data(::Nim{N, T}) where {N, T}
    C = hexcols(NIM_C[N], N)
    to = byte_tables(padimg(T, gf2_inverse(C, N)))
    from = byte_tables(padimg(T, C))
    z = zero(PolyElement{N, T, NIM_LOW[N] % T})
    return :(($to, $from, $z))
end

# The inclusion GF(2^m) ⊂ GF(2^N) as byte tables on rank bits (sources zero-extended to T).
@generated function nim_embed_table(::Val{M}, ::Nim{N, T}) where {M, N, T}
    return :($(byte_tables(padimg(T, hexcols(NIM_EMB[(M, N)], N)))))
end

# --- Arithmetic ----------------------------------------------------------------------------------

@stable default_mode = "error" begin
    @inline function to_nimpoly(a::Nim)
        to, _, z = nim_data(a)
        return unsafe_frombits(typeof(z), apply_bytes(to, bits(a)))
    end
    @inline function from_nimpoly(a::P, p::PolyElement) where {P <: Nim}
        _, from, _ = nim_data(a)
        return unsafe_frombits(P, apply_bytes(from, bits(p)))
    end

    mul(::CLMul, a::P, b::P) where {P <: Nim} = from_nimpoly(a, to_nimpoly(a) * to_nimpoly(b))
    Base.:*(a::P, b::P) where {P <: Nim} = mul(CLMul(), a, b)

    function Base.inv(a::Nim)
        iszero(a) && throw(DivideError())
        return from_nimpoly(a, inv(to_nimpoly(a)))
    end
end

default_strategy(::Type{<:Nim}) = CLMul()

# --- Inclusions, equality, promotion ------------------------------------------------------------

function embed(::Type{Q}, x::Nim{M, S}) where {Q <: Nim, M, S}
    N, T = degree(Q), storagetype(Q)
    N % M == 0 || throw(ArgumentError("GF(2^$M) does not embed into GF(2^$N): $M ∤ $N"))
    M == N && return Q(bits(x))
    return unsafe_frombits(Q, apply_bytes(nim_embed_table(Val(M), zero(Q)), bits(x) % T))
end

function embed(::Type{Q}, x::Nimber{K, S}) where {Q <: Nim, K, S}
    N, T = degree(Q), storagetype(Q)
    M = 1 << K
    N % M == 0 || throw(ArgumentError("GF(2^$M) does not embed into GF(2^$N): $M ∤ $N"))
    return unsafe_frombits(Q, apply_bytes(nim_embed_table(Val(M), zero(Q)), bits(x) % T))
end

# Conversions used by promotion: the inclusion (and restriction from a field to a subfield that
# contains the element).
function Nim{N, T}(x::Union{Nim, Nimber}) where {N, T}
    N % degree(typeof(x)) == 0 && return embed(Nim{N, T}, x)
    r = reduce_field(x)
    N % degree(typeof(r)) == 0 ||
        throw(ArgumentError("$x is not an element of GF(2^$N) (its smallest field is GF(2^$(degree(typeof(r)))))"))
    return embed(Nim{N, T}, r)
end
Nimber{K, T}(x::Nim) where {K, T} = Nimber{K, T}(reduce_field(x)::Nimber)

nim_lcm_type(::Val{L}) where {L} = L <= 128 ? nim_field(Val(L)) : Union{}
Base.promote_rule(::Type{Nim{M, S}}, ::Type{Nim{N, T}}) where {M, S, N, T} = nim_lcm_type(Val(lcm(M, N)))
Base.promote_rule(::Type{Nim{M, S}}, ::Type{Nimber{K, T}}) where {M, S, K, T} =
    nim_lcm_type(Val(lcm(M, 1 << K)))

const NIM_EMB_COLS = Dict(k => hexcols(v, k[2]) for (k, v) in NIM_EMB)

# --- Conway fields ------------------------------------------------------------------------------
#
# The isomorphism conway_field(n) ≅ nim_field(n) sends α_n to the root NIM_CONWAY_ROOT[n] of C_n
# in GF(2^n) ⊂ On_2: among the roots compatible with every α_m, m | n, the one of least rank
# (nimfield.md, "Conway fields"; for n = 2^k the root r_k of polyfield.md, so the nimber
# isomorphisms of polyfield.jl are the same maps). Below, n is not a power of two.

include("nim_conway_roots.jl")

gf2_apply(cols, v) = foldl((r, i) -> isodd(v >> (i - 1)) ? r ⊻ cols[i] : r, eachindex(cols); init = zero(UInt128))

# a * b mod (x^n + low) on coefficient bits, shift and add (cold: table construction only)
function gf2_mulmod(a::UInt128, b::UInt128, n::Int, low::UInt128)
    r = zero(UInt128)
    top = UInt128(1) << (n - 1)
    for _ in 1:n
        isodd(b) && (r ⊻= a)
        b >>= 1
        a = iszero(a & top) ? a << 1 : ((a << 1) ⊻ low) & mask_bits(n)
    end
    return r
end
mask_bits(n::Int) = n == 128 ? typemax(UInt128) : (UInt128(1) << n) - 1

# rank(α_n^i), i = 0 … n-1: the image of the Conway basis bit i in rank coordinates. The powers
# are taken in the internal basis 1, g, …, g^(n-1) (NIM_C: ranks of g^i; NIM_LOW: minpoly of g).
function nim_conway_cols(n::Int)
    C = hexcols(NIM_C[n], n)
    a = gf2_apply(gf2_inverse(C, n), get(() -> PSEUDO_CONWAY_ROOT[n], NIM_CONWAY_ROOT, n))
    cols, p = UInt128[], one(UInt128)
    for _ in 1:n
        push!(cols, gf2_apply(C, p))
        p = gf2_mulmod(p, a, n, NIM_LOW[n])
    end
    return cols
end

# Byte tables of the isomorphism: `from` Conway bits ↦ rank bits, `to` its inverse.
@generated function conway_nim_iso(::Val{N}) where {N}
    T = poly_storage(N)
    cols = nim_conway_cols(N)
    return :((to = $(byte_tables(padimg(T, gf2_inverse(cols, N)))), from = $(byte_tables(padimg(T, cols)))))
end

no_conway_embedding(x, Q) = throw(ArgumentError("no standard embedding of $(typeof(x)) into $Q"))

# Conway → nim_field: the isomorphism onto nim_field(m), then the inclusion of On_2.
function embed(::Type{Q}, x::P) where {Q <: Nim, P <: PolyElement}
    m, n = degree(P), degree(Q)
    (in_conway_system(P) && n % m == 0) || no_conway_embedding(x, Q)
    ispow2(m) && return embed(Q, embed(nim_field(Val(m)), x))      # through the nimber isomorphism
    y = unsafe_frombits(nim_field(Val(m)), apply_bytes(conway_nim_iso(Val(m)).from, bits(x)))
    return embed(Q, y)
end

# nim_field → Conway, degree n not a power of two: the inclusion into nim_field(n), then the
# inverse isomorphism. (Nimber sources of degree 2^k | n come here too, see polyfield.jl.)
function nim_to_conway(::Type{Q}, x::Union{Nim, Nimber}) where {Q <: PolyElement}
    n = degree(Q)
    y = embed(nim_field(Val(n)), x)
    return unsafe_frombits(Q, apply_bytes(conway_nim_iso(Val(n)).to, bits(y)))
end

function embed(::Type{Q}, x::Nim{M, S}) where {Q <: PolyElement, M, S}
    (in_conway_system(Q) && degree(Q) % M == 0) || no_conway_embedding(x, Q)
    return nim_to_conway(Q, x)
end

# minimal_degree(x::Nim): the smallest d | N with x^(2^d) = x (the smallest subfield of On_2
# containing x), by squaring in the internal polynomial basis.
@stable default_mode = "error" begin
    function minimal_degree(x::Nim{N, T}) where {N, T}
        p = to_nimpoly(x)
        y = p
        for d in 1:N
            y = y * y
            N % d == 0 && y == p && return d
        end
        return N
    end
end

"""
    reduce_field(x::Nim)

`x` as an element of its smallest field [`nim_field`](@ref)`(minimal_degree(x))` (a `Nimber` when
that degree is a power of two), the same ordinal, `== x`. Type-unstable by design, like the nimber
version.
"""
function reduce_field(x::Nim{N, T}) where {N, T}
    d = minimal_degree(x)
    d == N && return x
    cols = NIM_EMB_COLS[(d, N)]
    piv = Tuple{UInt128, UInt128}[]
    for i in 1:d
        r, c = cols[i], UInt128(1) << (i - 1)
        for (pr, pc) in piv
            !iszero(r & (UInt128(1) << (127 - leading_zeros(pr)))) && (r ⊻= pr; c ⊻= pc)
        end
        push!(piv, (r, c))
        sort!(piv; by = t -> leading_zeros(t[1]))
    end
    return nim_field(d)(gf2_solve(piv, UInt128(bits(x))))
end

# Same field: bits. Across fields: the same ordinal, i.e. the same smallest field and rank there.
Base.:(==)(x::P, y::P) where {P <: Nim} = bits(x) == bits(y)
nim_same(x, y) = minimal_degree(x) == minimal_degree(y) && bits(reduce_field(x)) == bits(reduce_field(y))
Base.:(==)(x::Nim, y::Nim) = nim_same(x, y)
Base.:(==)(x::Nim, y::Nimber) = nim_same(x, y)
Base.:(==)(x::Nimber, y::Nim) = nim_same(x, y)

# Hash the ordinal: through the smallest field, so that it agrees with `Nimber` (hash of the bits)
# whenever that field is a nimber field.
function Base.hash(x::Nim, h::UInt)
    r = reduce_field(x)
    r isa Nimber && return hash(r, h)
    return hash(bits(r), hash(degree(typeof(r)), hash(:Nim, h)))
end
