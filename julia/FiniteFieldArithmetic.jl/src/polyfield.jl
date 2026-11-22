# J1a: fields in a polynomial basis, GF(2)[x]/(f) with f = x^N + (low bits F), N ≤ 128; the
# Conway fields among them (f = C_N from Lübeck's table), the AES and GHASH fields, embeddings
# between Conway fields, and the isomorphisms between Conway and nimber fields of degree 2^k.
# Theory, conventions and measurements: polyfield.md beside this file.

"""
    PolyElement{N, T<:Unsigned, F} <: BinaryFieldElement

An element of ``\\mathbb{F}_2[x]/(f)`` with ``f = x^N + \\sum_i F_i x^i``, where the bits of
`F::T` are the coefficients of ``f`` below ``x^N``. The element is the polynomial
``\\sum_i b_i x^i`` of degree below ``N``, stored as its coefficient bits ``b`` in `T`, the
smallest unsigned type with at least `N` bits (`N ≤ 128`).

`f` must be irreducible; [`poly_field`](@ref)`(N, F)` checks this and returns the type. With
`f` the Conway polynomial ``C_N`` this is the Conway field, [`conway_field`](@ref)`(N)`, the
default representation for degrees that are not a power of two (ADR-0004). Also defined:
[`GF256_AES`](@ref), [`GF2_128_GHASH`](@ref).

Products use tables up to degree 16 and carry-less multiplication with Barrett reduction above
(`polyfield.md`, [`default_strategy`](@ref)); inverses use
[`default_inv_strategy`](@ref) (`src/inversion.md`). Elements of different fields are never equal; maps between fields
are explicit, through [`embed`](@ref).
"""
struct PolyElement{N, T <: Unsigned, F} <: BinaryFieldElement
    bits::T
    function PolyElement{N, T, F}(b::T, ::Val{:unchecked}) where {N, T <: Unsigned, F}
        check_poly_params(N, T, F)
        return new{N, T, F}(b)
    end
end

# The storage type of degree n: the smallest unsigned type with at least n bits.
function poly_storage(n::Int)
    1 <= n <= 8 && return UInt8
    n <= 16 && return UInt16
    n <= 32 && return UInt32
    n <= 64 && return UInt64
    n <= 128 && return UInt128
    throw(ArgumentError("polynomial-basis fields of degree $n are not implemented (1 ≤ n ≤ 128)"))
end

# Folded at compile time for valid parameters (all of them are type parameters).
@inline function check_poly_params(N, ::Type{T}, F) where {T}
    N isa Int || throw(ArgumentError("PolyElement: the degree must be an Int, got $N"))
    poly_storage(N) === T ||
        throw(ArgumentError("PolyElement{$N, $T}: GF(2^$N) is stored in $(poly_storage(N))"))
    F isa T || throw(ArgumentError("PolyElement{$N, $T, $F}: the modulus bits must be a $T"))
    (N == 8 * sizeof(T) || F >> N == 0) ||
        throw(ArgumentError("PolyElement{$N, $T, $F}: the modulus bits must be below x^$N"))
    return nothing
end

bits(x::PolyElement) = x.bits
storagetype(::Type{PolyElement{N, T, F}}) where {N, T, F} = T
degree(::Type{PolyElement{N, T, F}}) where {N, T, F} = N
unsafe_frombits(::Type{P}, b::T) where {N, T, F, P <: PolyElement{N, T, F}} = P(b, Val(:unchecked))

"""
    field_modulus(F::Type{<:PolyElement}) -> storagetype(F)

The coefficients of the modulus ``f`` below ``x^N`` as a bit pattern: ``f = x^N +``
`field_modulus(F)`. `0x1d` for the Conway field of degree 8 (``x^8 + x^4 + x^3 + x^2 + 1``).
"""
field_modulus(::Type{PolyElement{N, T, F}}) where {N, T, F} = F

function PolyElement{N, T, F}(n::Integer) where {N, T <: Unsigned, F}
    P = PolyElement{N, T, F}
    check_poly_params(N, T, F)
    0 <= n <= max_bits(P) ||
        throw(ArgumentError("$n is not an element of GF(2^$N) (needs 0 ≤ n < 2^$N)"))
    return unsafe_frombits(P, n % T)
end

# --- Products: carry-less multiplication and Barrett reduction ---------------------------------
#
# For p = a·b = H·x^N + L (deg p ≤ 2N - 2), the quotient of p by f is q = ⌊H·μ / x^N⌋ with
# μ = ⌊x^(2N) / f⌋ = x^N + μ′, i.e. q = H ⊕ ⌊H·μ′ / x^N⌋, and p mod f = L ⊕ (q·F mod x^N).
# (Barrett reduction for polynomials; exact, not approximate, over a field: polyfield.md.)

# μ′ = ⌊x^(2N) / f⌋ - x^N, computed once per type at compile time.
function barrett_mu_value(N::Int, F::Unsigned)
    f = (big(1) << N) | big(F)
    r, q = big(1) << (2N), big(0)
    while !iszero(r) && ndigits(r; base = 2) - 1 >= N
        s = ndigits(r; base = 2) - 1 - N
        q |= big(1) << s
        r = xor(r, f << s)
    end
    return (q & ((big(1) << N) - 1)) % typeof(F)
end
@generated barrett_mu(::Type{PolyElement{N, T, F}}) where {N, T, F} = :($(barrett_mu_value(N, F)))

const SmallStorage = Union{UInt8, UInt16, UInt32, UInt64}

@stable default_mode = "error" begin
    # The full carry-less product of two UInt128 as (high, low) words: Karatsuba, three products.
    @inline function clmul128(a::UInt128, b::UInt128)
        a1, a0 = (a >> 64) % UInt64, a % UInt64
        b1, b0 = (b >> 64) % UInt64, b % UInt64
        l = clmul64(a0, b0)
        h = clmul64(a1, b1)
        m = clmul64(a0 ⊻ a1, b0 ⊻ b1) ⊻ l ⊻ h
        return (h ⊻ (m >> 64), l ⊻ (m << 64))
    end
    # Its low word only.
    @inline function clmul128_lo(a::UInt128, b::UInt128)
        a1, a0 = (a >> 64) % UInt64, a % UInt64
        b1, b0 = (b >> 64) % UInt64, b % UInt64
        return clmul64(a0, b0) ⊻ ((clmul64(a0, b1) ⊻ clmul64(a1, b0)) << 64)
    end

    # (Elements, not types, as arguments: DispatchDoctor's @stable sees a Type{P} argument only
    # as DataType and would check the return type at runtime, about 2.4 µs per call.)
    @inline function poly_mul_bits(x::P, y::P) where {N, T <: SmallStorage, F,
                                                      P <: PolyElement{N, T, F}}
        μ = barrett_mu(P) % UInt64
        a, b = bits(x), bits(y)
        p = clmul64(a % UInt64, b % UInt64)
        H = (p >> N) % UInt64
        q = H ⊻ ((clmul64(H, μ) >> N) % UInt64)
        r = (p % UInt64) ⊻ (clmul64(q, F % UInt64) % UInt64)
        return r % T & max_bits(P)
    end

    @inline function poly_mul_bits(x::P, y::P) where {N, F, P <: PolyElement{N, UInt128, F}}
        μ = barrett_mu(P)
        hi, lo = clmul128(bits(x), bits(y))
        H = (lo >> N) | (hi << (128 - N))               # N = 128: lo >> 128 == 0
        th, tl = clmul128(H, μ)
        q = H ⊻ ((tl >> N) | (th << (128 - N)))
        return (lo ⊻ clmul128_lo(q, F)) & max_bits(P)
    end
end

@stable default_mode = "error" begin
    mul(::CLMul, a::P, b::P) where {P <: PolyElement} =
        unsafe_frombits(P, poly_mul_bits(a, b))

    Base.:*(a::P, b::P) where {P <: PolyElement} = mul(default_strategy(P), a, b)
end

@doc """
    mul(CLMul(), a::PolyElement, b::PolyElement)

The product in ``\\mathbb{F}_2[x]/(f)``: carry-less multiplication (`PCLMULQDQ` where the CPU
has it, [`has_pclmul`](@ref)) and Barrett reduction, two more carry-less products. The strategy
behind `*` from degree 17 up; below, [`default_strategy`](@ref) is a table
(`mul(MulTable(), a, b)` up to degree 8, `mul(LogTable(), a, b)` up to 16).
"""
mul(::CLMul, ::PolyElement, ::PolyElement)


# By degree, from bench/polytables.jl (polyfield.md, "Table strategies"): the full product table
# up to degree 8, logarithms up to 16 (3-5x the throughput of CLMul), CLMul above.
default_strategy(::Type{<:PolyElement{N}}) where {N} =
    N <= POLY_MULTABLE_MAX_DEGREE ? MulTable() : N <= POLY_LOGTABLE_MAX_DEGREE ? LogTable() : CLMul()

# --- Table strategies for small degrees (MulTable up to degree 8, LogTable up to 16) ------------
#
# Tables per field, built at compile time from the carry-less product and embedded as constants
# of generated code (as the Itoh–Tsujii tables, inversion.jl). MulTable: the product table as a
# vector indexed by (a << N) | b (no matrix: its size need not be reloaded), and an inverse table.
# LogTable: logarithms to the base of the least primitive element (x for a Conway field, so the
# logarithm is the Conway discrete logarithm), exponentials over 2(2^N - 1) entries so that a sum
# of two logarithms needs no reduction. polyfield.md, "Table strategies".

const POLY_MULTABLE_MAX_DEGREE = 8
const POLY_LOGTABLE_MAX_DEGREE = 16

# a^e with the carry-less product (the table builders must not depend on `*`, which may use them).
function clmul_pow(a::P, e::Integer) where {P <: PolyElement}
    r, b = one(P), a
    while e > 0
        isodd(e) && (r = mul(CLMul(), r, b))
        b = mul(CLMul(), b, b)
        e >>= 1
    end
    return r
end

# The least primitive element in the order of bit patterns (cold; N ≤ 16).
function least_primitive_bits(::Type{P}) where {N, T, F, P <: PolyElement{N, T, F}}
    q = (1 << N) - 1
    ps = [p for p in 2:q if q % p == 0 && all(p % d != 0 for d in 2:isqrt(p))]
    for b in 1:q
        g = unsafe_frombits(P, T(b))
        all(p -> !isone(clmul_pow(g, q ÷ p)), ps) && return T(b)
    end
    error("$P has no primitive element: the modulus is not irreducible")
end

"""
    log_generator(F::Type{<:PolyElement}) -> F

The base of the logarithms of [`LogTable`](@ref) on `F` (degree ≤ 16): the primitive element of
`F` with the least bit pattern. For a Conway field it is ``\\alpha_n = x``
([`conway_generator`](@ref)); for [`GF256_AES`](@ref) it is `0x03` (``x`` has order 51 there).
"""
function log_generator(::Type{P}) where {N, T, F, P <: PolyElement{N, T, F}}
    N <= POLY_LOGTABLE_MAX_DEGREE ||
        throw(ArgumentError("LogTable: tables only up to degree $POLY_LOGTABLE_MAX_DEGREE, not $N"))
    return unsafe_frombits(P, least_primitive_bits(P))
end

# (Element arguments, not types: see the note on @stable above.)
@generated function poly_mul_table(::P) where {N, T, F, P <: PolyElement{N, T, F}}
    N <= POLY_MULTABLE_MAX_DEGREE || return :(throw(ArgumentError(
        $("MulTable: product tables only up to degree $POLY_MULTABLE_MAX_DEGREE, not $N"))))
    q = 1 << N
    el(b) = unsafe_frombits(P, T(b))
    mt = T[bits(mul(CLMul(), el(a), el(b))) for a in 0:(q - 1) for b in 0:(q - 1)]  # (a << N) | b
    it = T[a == 0 ? zero(T) : bits(clmul_pow(el(a), q - 2)) for a in 0:(q - 1)]
    return :(($mt, $it))
end

@generated function poly_log_tables(::P) where {N, T, F, P <: PolyElement{N, T, F}}
    N <= POLY_LOGTABLE_MAX_DEGREE || return :(throw(ArgumentError(
        $("LogTable: tables only up to degree $POLY_LOGTABLE_MAX_DEGREE, not $N"))))
    q = (1 << N) - 1
    g = unsafe_frombits(P, least_primitive_bits(P))
    L = N <= 8 ? UInt8 : UInt16
    ex = Vector{T}(undef, 2q)
    lg = zeros(L, q + 1)
    x = one(P)
    for i in 0:(2q - 1)
        ex[i + 1] = bits(x)
        i < q && (lg[Int(bits(x)) + 1] = L(i))
        x = mul(CLMul(), x, g)
    end
    return :(($lg, $ex))
end

@stable default_mode = "error" begin
    @inline function mul(::MulTable, a::P, b::P) where {N, T, F, P <: PolyElement{N, T, F}}
        mt, _ = poly_mul_table(a)
        return unsafe_frombits(P, @inbounds mt[((Int(bits(a)) << N) | Int(bits(b))) + 1])
    end
    @inline function inverse(::MulTable, a::P) where {N, T, F, P <: PolyElement{N, T, F}}
        _, it = poly_mul_table(a)
        iszero(a) && throw(DivideError())
        return unsafe_frombits(P, @inbounds it[Int(bits(a)) + 1])
    end

    @inline function mul(::LogTable, a::P, b::P) where {N, T, F, P <: PolyElement{N, T, F}}
        lg, ex = poly_log_tables(a)
        (iszero(a) || iszero(b)) && return zero(P)
        @inbounds l = Int(lg[Int(bits(a)) + 1]) + Int(lg[Int(bits(b)) + 1])
        return unsafe_frombits(P, @inbounds ex[l + 1])
    end
    @inline function inverse(::LogTable, a::P) where {N, T, F, P <: PolyElement{N, T, F}}
        lg, ex = poly_log_tables(a)
        iszero(a) && throw(DivideError())
        q = (1 << N) - 1                             # a^(-1) = g^(q - log a), q - log a ∈ 1:q
        return unsafe_frombits(P, @inbounds ex[q - Int(lg[Int(bits(a)) + 1]) + 1])
    end
end

@doc """
    mul(MulTable(), a::PolyElement, b::PolyElement)
    inverse(MulTable(), a::PolyElement)

For a polynomial-basis field of degree ``N \\le 8``: lookup in the full product table
(``2^{2N}`` entries, 64 KiB at ``N = 8``) and an inverse table, built per field at compile time.
Throws `ArgumentError` above degree 8.
""" mul(::MulTable, ::PolyElement, ::PolyElement)

@doc """
    mul(LogTable(), a::PolyElement, b::PolyElement)
    inverse(LogTable(), a::PolyElement)

For a polynomial-basis field of degree ``N \\le 16``: ``ab = g^{\\log a + \\log b}`` and
``a^{-1} = g^{2^N - 1 - \\log a}`` with logarithm and exponential tables to the base
``g`` = [`log_generator`](@ref)`(F)` (``\\alpha_n = x`` for Conway fields), built per field at
compile time (384 KiB at ``N = 16``). Throws `ArgumentError` above degree 16.
""" mul(::LogTable, ::PolyElement, ::PolyElement)

# --- Constructing fields ----------------------------------------------------------------------

include("conway_table.jl")

"""
    conway_degrees() -> Vector{Int}

The degrees ``n \\le 128`` for which the Conway polynomial ``C_n`` over ``\\mathbb{F}_2`` is in
the package's table (Lübeck's database): every ``n \\le 92`` and some above, not 128.
"""
conway_degrees() = Int[n for (n, _) in CONWAY_TABLE]

"""
    is_conway(F::Type{<:BinaryFieldElement}) -> Bool

Whether `F` is a polynomial-basis field whose modulus is the Conway polynomial of its degree.
"""
is_conway(::Type{<:BinaryFieldElement}) = false

"""
    conway_field(n::Integer)
    conway_field(Val(n))

The Conway field ``\\mathbb{F}_{2^n} = \\mathbb{F}_2[x]/(C_n)`` as a [`PolyElement`](@ref) type.
`conway_field(Val(n))` is type-stable; `conway_field(n)` is not (its result is a type that
depends on the value). Throws `ArgumentError` for a degree not in the table
([`conway_degrees`](@ref)).

```jldoctest
julia> F = conway_field(8); F(0x02) * F(0x80)
0x1d
```
"""
function conway_field end

conway_field(::Val{n}) where {n} =
    throw(ArgumentError("no Conway polynomial of degree $n in the table (conway_degrees())"))

for (n, low) in CONWAY_TABLE
    T = poly_storage(n)
    P = PolyElement{n, T, low % T}
    @eval conway_field(::Val{$n}) = $P
    @eval is_conway(::Type{$P}) = true
end

const CONWAY_DEGREE_SET = BitSet(conway_degrees())

# --- Pseudo-Conway fields (the degrees missing from Lübeck's table) ----------------------------

include("pseudo_conway_table.jl")

"""
    pseudo_conway_degrees() -> Vector{Int}

The 15 degrees ``n \\le 128`` without a Conway polynomial in the table (93, 94, 99, …, 124, 128),
for which [`pseudo_conway_field`](@ref) is defined. Together with [`conway_degrees`](@ref) they
are `1:128`.
"""
pseudo_conway_degrees() = Int[t[1] for t in PSEUDO_CONWAY_TABLE]

"""
    is_pseudo_conway(F::Type{<:BinaryFieldElement}) -> Bool

Whether `F` is one of the [`pseudo_conway_field`](@ref)s.
"""
is_pseudo_conway(::Type{<:BinaryFieldElement}) = false

"""
    pseudo_conway_field(n::Integer)
    pseudo_conway_field(Val(n))

For a degree ``n \\le 128`` with no Conway polynomial in the table
([`pseudo_conway_degrees`](@ref)), the field ``\\mathbb{F}_2[x]/(P_n)`` with the **pseudo-Conway
polynomial** ``P_n`` defined from ``\\mathbf{On}_2`` (`polyfield.md`, "Pseudo-Conway fields"): in
``\\mathbb{F}_{2^n} \\subset \\mathbf{On}_2``, ``\\beta`` is the primitive element of least rank,
``\\rho_n = \\beta^k`` with ``k`` the least exponent prime to ``2^n - 1`` such that
``\\rho_n^{(2^n-1)/(2^m-1)}`` is the image of ``\\alpha_m`` for every ``m \\mid n``, and ``P_n``
is the minimal polynomial of ``\\rho_n``. So ``x`` is primitive, its norms are the Conway
generators of the subfields (Conway's compatibility), and [`embed`](@ref) treats these fields
exactly like the Conway fields. ``P_n`` is not the lexicographically least such polynomial, so it
need not equal a Conway polynomial computed later; hence the separate name.
"""
function pseudo_conway_field end

pseudo_conway_field(::Val{n}) where {n} =
    throw(ArgumentError("no pseudo-Conway polynomial of degree $n (pseudo_conway_degrees())"))
for (n, low) in PSEUDO_CONWAY_TABLE
    T = poly_storage(n)
    P = PolyElement{n, T, low % T}
    @eval pseudo_conway_field(::Val{$n}) = $P
    @eval is_pseudo_conway(::Type{$P}) = true
end
const PSEUDO_CONWAY_DEGREE_SET = BitSet(pseudo_conway_degrees())
const PSEUDO_CONWAY_ROOT = Dict{Int, UInt128}(t[1] => t[3] for t in PSEUDO_CONWAY_TABLE)

function pseudo_conway_field(n::Integer)
    n in PSEUDO_CONWAY_DEGREE_SET ||
        throw(ArgumentError("no pseudo-Conway polynomial of degree $n (pseudo_conway_degrees())"))
    return pseudo_conway_field(Val(Int(n)))
end

# The fields of the compatible system: Conway and pseudo-Conway (embed, conway_generator).
in_conway_system(::Type{F}) where {F} = is_conway(F) || is_pseudo_conway(F)

function conway_field(n::Integer)
    n in CONWAY_DEGREE_SET ||
        throw(ArgumentError("no Conway polynomial of degree $n in the table (conway_degrees())"))
    return conway_field(Val(Int(n)))
end

"""
    conway_generator(F::Type{<:PolyElement}) -> F

The class ``\\alpha_n`` of ``x`` in the Conway field `F` = [`conway_field`](@ref)`(n)`, a root of
``C_n`` and a generator of the multiplicative group; likewise for a
[`pseudo_conway_field`](@ref)`(n)` (a root of ``P_n``).
"""
function conway_generator(::Type{P}) where {N, T, F, P <: PolyElement{N, T, F}}
    in_conway_system(P) || throw(ArgumentError("$P is not a Conway or pseudo-Conway field"))
    return unsafe_frombits(P, N == 1 ? F : T(2))        # in degree 1, x = F (x + F = 0)
end

# Rabin's irreducibility test on f = x^n + low, with BigInt bit patterns (once per call, cold).
function is_irreducible_poly(n::Int, low::Integer)
    f = (big(1) << n) | big(low)
    deg(a) = iszero(a) ? -1 : ndigits(a; base = 2) - 1
    function pmod(a, g)
        while deg(a) >= deg(g)
            a = xor(a, g << (deg(a) - deg(g)))
        end
        return a
    end
    function mulmod(a, b)
        r = big(0)
        while !iszero(b)
            isodd(b) && (r = xor(r, a))
            a, b = a << 1, b >> 1
        end
        return pmod(r, f)
    end
    pgcd(a, b) = iszero(b) ? a : pgcd(b, pmod(a, b))
    x = pmod(big(2), f)
    xp = [x]                                         # x^(2^k) mod f, k = 0..n
    for _ in 1:n
        push!(xp, mulmod(xp[end], xp[end]))
    end
    xp[n + 1] == x || return false
    return all(p -> n % p != 0 || !all(q -> p % q != 0, 2:(p - 1)) ||
                    deg(pgcd(f, xor(xp[n ÷ p + 1], x))) == 0, 2:n)
end

"""
    poly_field(n::Integer, low::Integer)

The field ``\\mathbb{F}_2[x]/(f)``, ``f = x^n +`` `low` (the bits of `low` are the coefficients
below ``x^n``), as a [`PolyElement`](@ref) type. Checks that ``f`` is irreducible (Rabin's
test) and throws `ArgumentError` otherwise. Not type-stable.
`poly_field(8, 0x1b) === GF256_AES`; with the Conway polynomial it returns the Conway field.
"""
function poly_field(n::Integer, low::Integer)
    T = poly_storage(Int(n))
    0 <= low < big(2)^n || throw(ArgumentError("the modulus bits $low must be below 2^$n"))
    is_irreducible_poly(Int(n), low) ||
        throw(ArgumentError("x^$n + $(repr(low)) (as bits) is not irreducible over GF(2)"))
    return PolyElement{Int(n), T, low % T}
end

"""
The AES field ``\\mathbb{F}_2[x]/(x^8 + x^4 + x^3 + x + 1)`` (FIPS-197, Sec. 4.2), bytes as
coefficient bits: `GF256_AES(0x57) * GF256_AES(0x83) == GF256_AES(0xc1)`.
"""
const GF256_AES = PolyElement{8, UInt8, 0x1b}

"""
The GHASH field ``\\mathbb{F}_2[x]/(x^{128} + x^7 + x^2 + x + 1)`` (NIST SP 800-38D), with bit
``i`` of the `UInt128` the coefficient of ``x^i``. GCM itself stores the coefficients in the
reflected bit order (the coefficient of ``x^0`` in the most significant bit of the first byte);
convert with `bitreverse` at that boundary.
"""
const GF2_128_GHASH = PolyElement{128, UInt128, UInt128(0x87)}

# --- Embeddings -------------------------------------------------------------------------------

"""
    embed(G, x)

The image of `x` under the package's standard embedding of its field into `G`; defined when
`degree(typeof(x))` divides `degree(G)` and both fields belong to the compatible system:

- nimber into nimber: the inclusion (the same integer);
- Conway into Conway, ``\\mathbb{F}_{2^m} \\to \\mathbb{F}_{2^n}``: ``\\alpha_m \\mapsto
  \\alpha_n^{(2^n-1)/(2^m-1)}`` (the compatibility of Conway polynomials), computed through
  ``\\mathbb{F}_{2^n} \\subset \\mathbf{On}_2`` by byte tables;
- Conway into nimber and nimber into Conway, degree ``2^k \\le 64``: through the isomorphism
  that sends ``\\alpha_{2^k}`` to the root of ``C_{2^k}`` chosen in `polyfield.md`
  ("Nimbers and Conway fields"); these isomorphisms commute with the embeddings above;
- rank-encoded ([`nim_field`](@ref)) into rank-encoded: the inclusion of ``\\mathbf{On}_2``;
- Conway into [`nim_field`](@ref)`(n)` and back, every degree: through the isomorphism
  `conway_field(m)` ``\\cong`` `nim_field(m)` that sends ``\\alpha_m`` to the root of ``C_m``
  of least rank compatible with all ``\\alpha_d``, ``d \\mid m`` (`nimfield.md`, "Conway
  fields"; for ``m = 2^k`` the nimber isomorphism above), then the inclusion of
  ``\\mathbf{On}_2``. A Conway source needs only its own ``C_m`` (`nim_field(93)` has no Conway
  field, but receives `conway_field(31)`); a Conway target needs ``C_n``.

Throws `ArgumentError` otherwise (other polynomial bases such as [`GF256_AES`](@ref) have no
standard embedding: there are ``n`` isomorphisms and no reason to prefer one).
"""
function embed end

embed(::Type{G}, x::BinaryFieldElement) where {G <: BinaryFieldElement} =
    throw(ArgumentError("no standard embedding of $(typeof(x)) into $G"))

function embed(::Type{N}, x::Nimber) where {N <: Nimber}
    degree(typeof(x)) <= degree(N) ||
        throw(ArgumentError("GF(2^$(degree(typeof(x)))) does not embed into GF(2^$(degree(N)))"))
    return N(x)
end

# (2^n - 1)/(2^m - 1) = Σ_{i < n/m} 2^(m i) for m | n, in UInt128 (it is below 2^n ≤ 2^128).
conway_exponent(m::Int, n::Int) = foldl((e, i) -> e | (UInt128(1) << (m * i)), 0:(n ÷ m - 1);
                                        init = zero(UInt128))

function embed(::Type{Q}, x::P) where {P <: PolyElement, Q <: PolyElement}
    m, n = degree(P), degree(Q)
    (in_conway_system(P) && in_conway_system(Q)) ||
        throw(ArgumentError("no standard embedding of $P into $Q (both must be Conway fields)"))
    n % m == 0 || throw(ArgumentError("GF(2^$m) does not embed into GF(2^$n): $m ∤ $n"))
    P === Q && return Q(bits(x))
    # through GF(2^n) ⊂ On_2: the isomorphism onto nim_field(m), the inclusion, the inverse
    # isomorphism (nimfield.jl; the isomorphisms commute with the definition below by the choice
    # of the roots, and test/conway.jl checks agreement with embed_horner for every pair)
    return embed(Q, embed(nim_field(Val(n)), x))
end

# The Conway embedding by its definition, α_m ↦ α_n^((2^n-1)/(2^m-1)), evaluated by Horner on the
# coefficients of x (335 ns – 2.4 µs per element): the reference for the tests.
function embed_horner(::Type{Q}, x::P) where {P <: PolyElement, Q <: PolyElement}
    m, n = degree(P), degree(Q)
    (in_conway_system(P) && in_conway_system(Q) && n % m == 0) ||
        throw(ArgumentError("no Conway embedding of $P into $Q"))
    β = conway_generator(Q)^conway_exponent(m, n)
    # Horner on the coefficients of x, highest first
    r = zero(Q)
    for i in (m - 1):-1:0
        r = r * β
        isodd(bits(x) >> i) && (r += one(Q))
    end
    return r
end

# --- Nimbers and Conway fields ----------------------------------------------------------------
#
# The isomorphism φ_k : conway_field(2^k) → Nimber{k} sends α_{2^k} to a root r_k of C_{2^k}.
# Compatibility with the embeddings asks r_k^(2^(2^(k-1)) + 1) = r_{k-1}; of the 2^k roots
# exactly two satisfy it (r and its conjugate over the level below), and we take the smaller as
# an integer (polyfield.md). r_0 = 1.

const NIMBER_LEVELS = (GF2, GF4, GF16, GF256, GF2_16, GF2_32, GF2_64, GF2_128)

function conway_nimber_root(k::Int, rprev)
    N = NIMBER_LEVELS[k + 1]
    n = degree(N)
    k == 0 && return one(N)
    C = conway_field(n)
    low = field_modulus(C)
    exps = [i for i in 0:(n - 1) if isodd(low >> i)]
    r = N(find_root(N, exps))
    roots = [r]
    for _ in 2:n
        push!(roots, roots[end] * roots[end])
    end
    e = (UInt128(1) << (n ÷ 2)) + 1
    good = filter(s -> s^e == N(rprev), roots)
    length(good) == 2 || error("Conway–nimber isomorphism: $(length(good)) compatible roots at level $k")
    return minimum(bits, good) |> b -> N(b)
end

const CONWAY_NIMBER_ROOTS = let rs = Any[]
    for k in 0:6
        push!(rs, conway_nimber_root(k, k == 0 ? nothing : rs[end]))
    end
    Tuple(rs)
end

# Byte tables of φ_k (`from`: Conway bits ↦ nimber bits) and φ_k⁻¹ (`to`).
const CONWAY_NIMBER_ISO = ntuple(k -> PolyBasis(NIMBER_LEVELS[k], CONWAY_NIMBER_ROOTS[k]), 7)

# Level 7: pseudo_conway_field(128) ≅ GF(2^128), α ↦ ρ_128 (pseudo_conway_table.jl).
const PSEUDO_NIMBER_ISO_128 = PolyBasis(GF2_128, GF2_128(PSEUDO_CONWAY_ROOT[128]))

conway_iso(::Val{K}) where {K} = K <= 6 ? CONWAY_NIMBER_ISO[K + 1] : K == 7 ? PSEUDO_NIMBER_ISO_128 :
    throw(ArgumentError("no Conway or pseudo-Conway polynomial of degree 2^$K"))

function embed(::Type{N}, x::P) where {N <: Nimber, P <: PolyElement}
    m = degree(P)
    (in_conway_system(P) && ispow2(m) && m <= degree(N)) ||
        throw(ArgumentError("no standard embedding of $P into $N"))
    K = trailing_zeros(m)
    M = NIMBER_LEVELS[K + 1]
    y = unsafe_frombits(M, apply_bytes(conway_iso(Val(K)).from, bits(x)))
    return N(y)
end

function embed(::Type{Q}, x::Nimber{K, T}) where {Q <: PolyElement, K, T}
    n = degree(Q)
    (in_conway_system(Q) && n % (1 << K) == 0) ||
        throw(ArgumentError("no standard embedding of $(typeof(x)) into $Q"))
    ispow2(n) || return nim_to_conway(Q, x)          # through GF(2^n) ⊂ On_2 (nimfield.jl)
    L = trailing_zeros(n)                            # the nimber inclusion, then φ_L⁻¹
    y = NIMBER_LEVELS[L + 1](x)
    return unsafe_frombits(Q, apply_bytes(conway_iso(Val(L)).to, bits(y)))
end
