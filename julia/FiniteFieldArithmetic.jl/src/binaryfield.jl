# What every representation of a field of characteristic 2 shares: the element is a bit pattern,
# addition is XOR, negation is the identity, printing is hexadecimal. A representation
# (nimbers now; Conway and standard polynomial bases later) subtypes `BinaryFieldElement` and
# provides `bits`, `storagetype`, `degree`, `unsafe_frombits`, `*` and `inv`.

"""
    BinaryFieldElement <: Number

Supertype of elements of finite fields of characteristic 2, ``\\mathbb{F}_{2^n}``, stored as a
bit pattern in an unsigned integer. Subtypes provide [`bits`](@ref), [`degree`](@ref),
`storagetype`, `unsafe_frombits`, `*` and `inv`; addition (XOR), subtraction, negation,
equality, hashing, powers, division and hexadecimal printing are defined here once for all of
them.
"""
abstract type BinaryFieldElement <: Number end

"""
    bits(x::BinaryFieldElement)

The bit pattern of `x`, an unsigned integer of the field's storage type.
"""
function bits end

"""
    degree(F::Type{<:BinaryFieldElement})

The degree ``n`` of ``F = \\mathbb{F}_{2^n}`` over ``\\mathbb{F}_2``.
"""
function degree end

"""
    characteristic(F::Type{<:BinaryFieldElement}) = 2
"""
characteristic(::Type{<:BinaryFieldElement}) = 2

"""
    elements(F::Type{<:BinaryFieldElement})

All ``2^n`` elements of `F`, in the order of their bit patterns.
"""
elements(::Type{F}) where {F <: BinaryFieldElement} = Elements{F}()

# The iterator of `elements`. A range `0:max_bits(F)` would be wrong from GF(2^64) on: its length
# 2^n does not fit in an Int (nor in the storage type, where it wraps to 0). So the length is
# reported only when it fits in an Int; above that the size is unknown (the iteration is endless
# in practice) and `Iterators.take`/`first(_, k)` still work.
struct Elements{F <: BinaryFieldElement} end
Base.eltype(::Type{Elements{F}}) where {F} = F
Base.IteratorSize(::Type{Elements{F}}) where {F} =
    degree(F) < 8 * sizeof(Int) - 1 ? Base.HasLength() : Base.SizeUnknown()
function Base.length(::Elements{F}) where {F}
    n = degree(F)
    n < 8 * sizeof(Int) - 1 || throw(OverflowError("GF(2^$n) has 2^$n elements, more than typemax(Int)"))
    return 1 << n
end
Base.iterate(::Elements{F}) where {F} = (zero(F), zero(storagetype(F)))
function Base.iterate(::Elements{F}, b) where {F}
    b == max_bits(F) && return nothing
    b += one(b)
    return unsafe_frombits(F, b), b
end

# Whether the bit pattern fills the storage type (GF(256) in a UInt8 does, GF(16) does not).
fills_storage(::Type{F}) where {F <: BinaryFieldElement} = degree(F) == 8 * sizeof(storagetype(F))

# The largest bit pattern, 2^n - 1, in the storage type (no wider integer needed, even for
# GF(2^128), where it is typemax(UInt128)).
function max_bits(::Type{F}) where {F <: BinaryFieldElement}
    S = storagetype(F)
    return fills_storage(F) ? typemax(S) : (one(S) << degree(F)) - one(S)
end

# Order of the multiplicative group, 2^n - 1, in the storage type.
multiplicative_order(::Type{F}) where {F <: BinaryFieldElement} = max_bits(F)

@stable default_mode = "error" begin
    Base.:+(x::F, y::F) where {F <: BinaryFieldElement} = unsafe_frombits(F, bits(x) ⊻ bits(y))
    Base.:-(x::F, y::F) where {F <: BinaryFieldElement} = x + y
    Base.:-(x::BinaryFieldElement) = x
    Base.conj(x::BinaryFieldElement) = x
    Base.zero(::Type{F}) where {F <: BinaryFieldElement} = unsafe_frombits(F, zero(storagetype(F)))
    Base.one(::Type{F}) where {F <: BinaryFieldElement} = unsafe_frombits(F, one(storagetype(F)))
    Base.iszero(x::BinaryFieldElement) = iszero(bits(x))
    Base.isone(x::BinaryFieldElement) = isone(bits(x))
    Base.:(==)(x::F, y::F) where {F <: BinaryFieldElement} = bits(x) == bits(y)
    Base.:/(x::F, y::F) where {F <: BinaryFieldElement} = x * inv(y)

    function Base.:^(x::BinaryFieldElement, n::Integer)
        if iszero(x)
            n < 0 && throw(DivideError())
            return n == 0 ? one(x) : x
        end
        # x^q = 1 for x ≠ 0 and q = 2^n - 1, so the exponent only matters modulo q. The reduced
        # exponent is computed in the storage type S (q fits there); for n < 0, with
        # m = (-(n + 1)) mod q, one has n ≡ -(m + 1) ≡ q - 1 - m, which never under- or overflows.
        S = storagetype(typeof(x))
        q = multiplicative_order(typeof(x))
        e = n >= 0 ? S(rem(n, q)) : q - one(S) - S(rem(-(n + 1), q))
        return Base.power_by_squaring(x, e)
    end
end

# Elements of different types are compared in their common promotion, if there is one (nimber
# levels: the larger level, since the subfields are nested). Unrelated representations promote to
# no concrete type and are never equal: there is no implicit isomorphism between them.
function Base.:(==)(x::BinaryFieldElement, y::BinaryFieldElement)
    P = promote_type(typeof(x), typeof(y))
    isconcretetype(P) || return false
    return convert(P, x) == convert(P, y)
end

# A field element is never equal to an integer, a float or any other number: there is no ring
# map that would make the comparison meaningful in general (an integer could mean a bit pattern
# or the image of ℤ). Returning false rather than throwing keeps `in`, `Set` and `Dict` working
# on mixed collections.
Base.:(==)(::BinaryFieldElement, ::Number) = false
Base.:(==)(::Number, ::BinaryFieldElement) = false

# Hash the bit pattern only: representations whose subfields are nested as integers (nimbers)
# compare equal across levels, so their hashes must agree too.
Base.hash(x::BinaryFieldElement, h::UInt) = hash(bits(x), hash(:BinaryFieldElement, h))

# Uniform random elements.
function Random.rand(rng::Random.AbstractRNG, ::Random.SamplerType{F}) where {F <: BinaryFieldElement}
    return unsafe_frombits(F, rand(rng, storagetype(F)) & max_bits(F))
end

# Printing: hexadecimal, one digit per four bits of the field (maintainer, 2026-11-19).
function Base.print(io::IO, x::BinaryFieldElement)
    n = degree(typeof(x))
    print(io, "0x", string(bits(x); base = 16, pad = cld(n, 4)))
    return nothing
end

# In the REPL the field is named when the hex value alone does not determine it (the field does
# not fill its storage), unless the context already states the element type (typed arrays).
function Base.show(io::IO, x::BinaryFieldElement)
    F = typeof(x)
    print(io, x)
    if !fills_storage(F) && get(io, :typeinfo, Any) !== F
        n = degree(F)
        print(io, n == 1 ? " ∈ GF(2)" : " ∈ GF(2^$n)")
    end
    return nothing
end
