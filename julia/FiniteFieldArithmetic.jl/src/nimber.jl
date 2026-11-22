# Nimber fields GF(2^(2^K)), K = 0..7. Theory, algorithms and measurements: nimber.md beside
# this file.

"""
    Nimber{K, T<:Unsigned} <: BinaryFieldElement

An element of the nimber field ``\\mathbb{F}_{2^{2^K}}``: the integers ``0 \\le a < 2^{2^K}``
with nim-addition (XOR) and nim-multiplication (Conway, *On Numbers and Games*, ch. 6), stored in
`T`, the smallest unsigned type that fits: `UInt8` for ``K \\le 3``, then `UInt16`, `UInt32`,
`UInt64`, `UInt128` for ``K = 4, \\dots, 7``.

The nimber fields are nested *as integers*: ``\\mathbb{F}_{2^{2^K}}`` consists of the integers
below ``2^{2^K}``, so the embedding into a larger nimber field keeps the bit pattern. Mixed
arithmetic promotes to the larger field accordingly, and elements of different levels with the
same value compare equal.

The default representation of the fields ``\\mathbb{F}_{2^{2^K}}`` (ADR-0004). Aliases:
[`GF2`](@ref), [`GF4`](@ref), [`GF16`](@ref), [`GF256`](@ref), [`GF2_16`](@ref),
[`GF2_32`](@ref), [`GF2_64`](@ref), [`GF2_128`](@ref).

Construct from the integer value (= the bit pattern): `GF256(0x1b)`, `GF2_64(27)`.
"""
struct Nimber{K, T <: Unsigned} <: BinaryFieldElement
    bits::T
    function Nimber{K, T}(b::T, ::Val{:unchecked}) where {K, T <: Unsigned}
        nimber_storage(K) === T || throw(ArgumentError(
            "Nimber{$K, $T}: GF(2^$(2^K)) is stored in $(nimber_storage(K))"))
        return new{K, T}(b)
    end
end

"""GF(2) as nimbers: `Nimber{0, UInt8}`."""
const GF2 = Nimber{0, UInt8}
"""GF(4) as nimbers: `Nimber{1, UInt8}`; contains [`GF2`](@ref) as the values 0, 1."""
const GF4 = Nimber{1, UInt8}
"""GF(16) as nimbers: `Nimber{2, UInt8}`; contains [`GF4`](@ref) as the values 0–3."""
const GF16 = Nimber{2, UInt8}
"""GF(256) as nimbers: `Nimber{3, UInt8}`; contains [`GF16`](@ref) as the values 0–15."""
const GF256 = Nimber{3, UInt8}
"""GF(2^16) as nimbers: `Nimber{4, UInt16}`; contains [`GF256`](@ref) as the values below 2^8."""
const GF2_16 = Nimber{4, UInt16}
"""GF(2^32) as nimbers: `Nimber{5, UInt32}`; contains [`GF2_16`](@ref) as the values below 2^16."""
const GF2_32 = Nimber{5, UInt32}
"""GF(2^64) as nimbers: `Nimber{6, UInt64}`; contains [`GF2_32`](@ref) as the values below 2^32."""
const GF2_64 = Nimber{6, UInt64}
"""GF(2^128) as nimbers: `Nimber{7, UInt128}`; contains [`GF2_64`](@ref) as the values below 2^64."""
const GF2_128 = Nimber{7, UInt128}

# The storage type of level K: the smallest unsigned type with at least 2^K bits.
function nimber_storage(K::Int)
    0 <= K <= 3 && return UInt8
    K == 4 && return UInt16
    K == 5 && return UInt32
    K == 6 && return UInt64
    K == 7 && return UInt128
    throw(ArgumentError("nimber fields above GF(2^128) (level $K) are not implemented yet"))
end

# The storage type of the subfield one level down, used for the halves in the recursions.
halftype(::Type{UInt8}) = UInt8
halftype(::Type{UInt16}) = UInt8
halftype(::Type{UInt32}) = UInt16
halftype(::Type{UInt64}) = UInt32
halftype(::Type{UInt128}) = UInt64

bits(x::Nimber) = x.bits
storagetype(::Type{Nimber{K, T}}) where {K, T} = T
degree(::Type{Nimber{K, T}}) where {K, T} = 1 << K
unsafe_frombits(::Type{Nimber{K, T}}, b::T) where {K, T} = Nimber{K, T}(b, Val(:unchecked))

function Nimber{K, T}(n::Integer) where {K, T <: Unsigned}
    N = Nimber{K, T}
    nimber_storage(K) === T || throw(ArgumentError(
        "Nimber{$K, $T}: GF(2^$(2^K)) is stored in $(nimber_storage(K))"))
    0 <= n <= max_bits(N) ||
        throw(ArgumentError("$n is not an element of GF(2^$(1 << K)) (needs 0 ≤ n < 2^$(1 << K))"))
    return unsafe_frombits(N, n % T)
end

# Embedding into a larger level keeps the bits; restriction to a smaller one checks they fit.
Nimber{K, T}(x::Nimber) where {K, T <: Unsigned} = Nimber{K, T}(bits(x))

Base.promote_rule(::Type{Nimber{K1, T1}}, ::Type{Nimber{K2, T2}}) where {K1, T1, K2, T2} =
    K1 >= K2 ? Nimber{K1, T1} : Nimber{K2, T2}

# --- Strategies -----------------------------------------------------------------------------

"""
    MulStrategy

How multiplication and inversion are computed. Every strategy gives the same results; they
differ in speed and memory, measured in `bench/` and recorded in `src/nimber.md`.

All strategies share one recursion over the levels (Karatsuba-style: three half-size products
and one product with a constant, see [`Recursive`](@ref)); they differ in the level where the
recursion stops:

- [`Recursive`](@ref): down to ``\\mathbb{F}_2``, no tables.
- [`MulTable`](@ref): down to ``\\mathbb{F}_{256}``, then a full 256 × 256 product table
  (64 KiB) and a 256-entry inverse table.
- [`LogTable`](@ref): down to ``\\mathbb{F}_{256}``, then logarithm and exponential tables
  (768 bytes).

Since the subfields are nested as integers, the tables of ``\\mathbb{F}_{256}`` serve every level
up to it unchanged.
"""
abstract type MulStrategy end

"""
    Recursive()

Nim-multiplication by recursion over the levels, down to ``\\mathbb{F}_2``. With
``h = 2^{K-1}``, ``F = 2^h`` and ``a = a_1 F + a_0``, ``b = b_1 F + b_0`` (halves in the subfield
of level ``K-1``): ``a \\otimes b = (e \\oplus d)\\,F + (d \\oplus c \\otimes F/2)`` with
``c = a_1 \\otimes b_1``, ``d = a_0 \\otimes b_0``,
``e = (a_0 \\oplus a_1) \\otimes (b_0 \\oplus b_1)``, because ``F \\otimes F = F \\oplus F/2``;
the product with the constant ``F/2`` has its own, cheaper recursion. Inversion uses the norm to
the subfield. No memory beyond registers; the reference implementation for the table strategies.
"""
struct Recursive <: MulStrategy end

"""
    MulTable()

The recursion of [`Recursive`](@ref) down to ``\\mathbb{F}_{256}``, then lookup in a full product
table (64 KiB) and an inverse table.
"""
struct MulTable <: MulStrategy end

"""
    LogTable()

The recursion of [`Recursive`](@ref) down to ``\\mathbb{F}_{256}``, then
``a \\otimes b = \\exp(\\log a + \\log b)`` with logarithm and exponential tables for a fixed
generator of ``\\mathbb{F}_{256}^\\times``; zero handled separately.
"""
struct LogTable <: MulStrategy end

const TableStrategy = Union{MulTable, LogTable}

# The levels the tables cover: GF(2) … GF(256).
const TableLevel = Union{Val{0}, Val{1}, Val{2}, Val{3}}

level(::Val{K}) where {K} = K

"""
    default_strategy(F)

The strategy behind `*` for `F`, chosen by the benchmarks in `bench/` (`src/nimber.md` and
`src/nimber_fast.md`, "Measurements"): [`CLMul`](@ref) for GF(2^128) (it computes as
[`MulTable`](@ref) on CPUs without `PCLMULQDQ`), [`MulTable`](@ref) for the other levels.
`inv` has its own default, [`default_inv_strategy`](@ref). For polynomial-basis fields
([`PolyElement`](@ref)): [`MulTable`](@ref) up to degree 8, [`LogTable`](@ref) up to 16,
[`CLMul`](@ref) above (`src/polyfield.md`, "Table strategies").
"""
default_strategy(::Type{<:Nimber}) = MulTable()
default_strategy(::Type{GF2_128}) = CLMul()

"""
    default_inv_strategy(F)

The strategy behind `inv` (and so `/`) for `F`. It is [`default_strategy`](@ref)`(F)` except
where inversion is measurably faster with another strategy: [`LogTable16`](@ref) at GF(2^16) and
GF(2^32) (one table lookup pair at GF(2^16), one norm step above it; `src/nimber_fast.md`,
"Default for inv"). Override it for a field like `default_strategy`.
"""
default_inv_strategy(::Type{F}) where {F <: Nimber} = default_strategy(F)

# --- The recursion, shared by all strategies --------------------------------------------------
#
# Functions on bit patterns: nim_mul_bits(s, a, b, Val(K)) is the product of a, b < 2^(2^K),
# nim_mul_half(s, c, Val(k)) is c ⊗ 2^(2^k - 1), nim_inv_bits(s, a, Val(K)) the inverse of a ≠ 0.
# Each has a generic recursive step (any strategy, any level) and base cases per strategy, which
# are more specific in both the strategy and the level: Recursive stops at level 0, the table
# strategies at the table levels 0–3. The halves are narrowed to the storage type of the level
# below (`halftype`), so no integer is wider than its level needs.

@stable default_mode = "error" begin
    @inline function nim_mul_bits(s::MulStrategy, a::T, b::T, ::Val{K}) where {T <: Unsigned, K}
        S = halftype(T)
        h = 1 << (K - 1)                      # half the degree
        lo = (one(T) << h) - one(T)
        a1, a0 = (a >> h) % S, (a & lo) % S
        b1, b0 = (b >> h) % S, (b & lo) % S
        c = nim_mul_bits(s, a1, b1, Val(K - 1))
        d = nim_mul_bits(s, a0, b0, Val(K - 1))
        e = nim_mul_bits(s, a0 ⊻ a1, b0 ⊻ b1, Val(K - 1))
        return (((e ⊻ d) % T) << h) | ((d ⊻ nim_mul_half(s, c, Val(K - 1))) % T)
    end

    # c ⊗ 2^(2^k - 1) for c < 2^(2^k): the product with the constant F/2 of the level above.
    # With F′ = 2^(2^(k-1)) one has 2^(2^k - 1) = F′ ⊗ (F′/2), and for c = c1 F′ + c0:
    # c ⊗ F′ = (c1 ⊕ c0) F′ ⊕ c1 ⊗ F′/2, so
    #   H_k(c) = H_{k-1}(c1 ⊕ c0) F′ + H_{k-1}(H_{k-1}(c1)),   H_0(c) = c.
    @inline function nim_mul_half(s::MulStrategy, c::T, ::Val{k}) where {T <: Unsigned, k}
        S = halftype(T)
        h = 1 << (k - 1)
        lo = (one(T) << h) - one(T)
        c1, c0 = (c >> h) % S, (c & lo) % S
        return ((nim_mul_half(s, c1 ⊻ c0, Val(k - 1)) % T) << h) |
               (nim_mul_half(s, nim_mul_half(s, c1, Val(k - 1)), Val(k - 1)) % T)
    end

    # Inverse of a ≠ 0. For a = a1 F + a0, the conjugate over the subfield is a1 F + (a0 ⊕ a1)
    # and the norm N = a1² ⊗ F/2 ⊕ a0 ⊗ a1 ⊕ a0² lies in the subfield, so
    # a⁻¹ = (a1 ⊗ N⁻¹) F + ((a0 ⊕ a1) ⊗ N⁻¹).
    @inline function nim_inv_bits(s::MulStrategy, a::T, ::Val{K}) where {T <: Unsigned, K}
        S = halftype(T)
        h = 1 << (K - 1)
        lo = (one(T) << h) - one(T)
        a1, a0 = (a >> h) % S, (a & lo) % S
        N = nim_mul_half(s, nim_mul_bits(s, a1, a1, Val(K - 1)), Val(K - 1)) ⊻
            nim_mul_bits(s, a0, a1, Val(K - 1)) ⊻ nim_mul_bits(s, a0, a0, Val(K - 1))
        Ninv = nim_inv_bits(s, N, Val(K - 1))
        return ((nim_mul_bits(s, a1, Ninv, Val(K - 1)) % T) << h) |
               (nim_mul_bits(s, a0 ⊻ a1, Ninv, Val(K - 1)) % T)
    end

    # Base cases of Recursive: level 0 is GF(2), where the product is AND and 1 is its own inverse.
    @inline nim_mul_bits(::Recursive, a::T, b::T, ::Val{0}) where {T <: Unsigned} = a & b
    @inline nim_mul_half(::Recursive, c::T, ::Val{0}) where {T <: Unsigned} = c
    @inline nim_inv_bits(::Recursive, a::T, ::Val{0}) where {T <: Unsigned} = a

    # Base cases of the table strategies: levels 0–3, values below 256, looked up in the GF(256)
    # tables (`a % UInt8` truncates without a check; the value fits by the level).
    @inline nim_mul_bits(::MulTable, a::T, b::T, ::TableLevel) where {T <: Unsigned} =
        (@inbounds NIM256_MUL[Int(a % UInt8) + 1, Int(b % UInt8) + 1]) % T
    @inline function nim_mul_bits(::LogTable, a::T, b::T, ::TableLevel) where {T <: Unsigned}
        (iszero(a) || iszero(b)) && return zero(T)
        @inbounds l = Int(NIM256_LOG[Int(a % UInt8) + 1]) + Int(NIM256_LOG[Int(b % UInt8) + 1])
        return (@inbounds NIM256_EXP[l + 1]) % T
    end
    @inline nim_mul_half(s::TableStrategy, c::T, v::TableLevel) where {T <: Unsigned} =
        nim_mul_bits(s, c, one(T) << ((1 << level(v)) - 1), v)
    @inline nim_inv_bits(::MulTable, a::T, ::TableLevel) where {T <: Unsigned} =
        (@inbounds NIM256_INV[Int(a % UInt8) + 1]) % T
    @inline nim_inv_bits(::LogTable, a::T, ::TableLevel) where {T <: Unsigned} =
        (@inbounds NIM256_EXP[255 - Int(NIM256_LOG[Int(a % UInt8) + 1]) + 1]) % T
end

# --- Tables (built once, at precompile time, with Recursive) --------------------------------

const NIM256_MUL = [nim_mul_bits(Recursive(), UInt8(a), UInt8(b), Val(3)) for a in 0:255, b in 0:255]
const NIM256_INV = [a == 0 ? 0x00 : nim_inv_bits(Recursive(), UInt8(a), Val(3)) for a in 0:255]

# The smallest generator of the multiplicative group of GF(256), and its log/exp tables.
# EXP has 510 entries so that EXP[log a + log b + 1] needs no reduction modulo 255.
const NIM256_GENERATOR = let
    order(g) = (x = g; k = 1; while x != 0x01; x = NIM256_MUL[x + 1, g + 1]; k += 1; end; k)
    UInt8(findfirst(g -> order(UInt8(g)) == 255, 2:255) + 1)
end
const NIM256_EXP = let e = zeros(UInt8, 510), x = 0x01
    for i in 1:510
        e[i] = x
        x = NIM256_MUL[x + 1, NIM256_GENERATOR + 1]
    end
    e
end
const NIM256_LOG = let l = zeros(UInt8, 256)
    for i in 0:254
        l[NIM256_EXP[i + 1] + 1] = UInt8(i)
    end
    l
end

# --- mul and inverse ------------------------------------------------------------------------

"""
    mul(strategy::MulStrategy, a, b)

The product `a * b` computed with `strategy`. `a * b` uses [`default_strategy`](@ref).
"""
function mul end

"""
    inverse(strategy::MulStrategy, a)

The multiplicative inverse of `a` computed with `strategy`; throws `DivideError` for zero.
`inv(a)` uses [`default_inv_strategy`](@ref).
"""
function inverse end

@stable default_mode = "error" begin
    mul(s::MulStrategy, a::N, b::N) where {K, T, N <: Nimber{K, T}} =
        unsafe_frombits(N, nim_mul_bits(s, bits(a), bits(b), Val(K)))

    function inverse(s::MulStrategy, a::N) where {K, T, N <: Nimber{K, T}}
        iszero(a) && throw(DivideError())
        return unsafe_frombits(N, nim_inv_bits(s, bits(a), Val(K)))
    end

    Base.:*(a::N, b::N) where {N <: Nimber} = mul(default_strategy(N), a, b)
    Base.inv(a::Nimber) = inverse(default_inv_strategy(typeof(a)), a)
end
