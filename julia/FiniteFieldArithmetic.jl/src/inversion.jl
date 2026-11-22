# J3: inversion strategies for every representation: Fermat (square and multiply), Itoh–Tsujii
# (an addition chain with Frobenius powers as byte tables), extended Euclid (in a polynomial
# basis). Theory and measurements: inversion.md beside this file.

"""
    InvStrategy

How [`inverse`](@ref) computes ``a^{-1}``, independently of the representation:
[`Fermat`](@ref), [`ItohTsujii`](@ref), [`Euclid`](@ref). (The multiplication strategies,
[`MulStrategy`](@ref), also invert nimbers, by the norm recursion.) `inv` uses
[`default_inv_strategy`](@ref).
"""
abstract type InvStrategy end

"""
    Fermat()

``a^{-1} = a^{2^n - 2}`` by square-and-multiply with `*`: about ``2n`` products. The reference
strategy, for any field.
"""
struct Fermat <: InvStrategy end

"""
    ItohTsujii()

Itoh–Tsujii: ``a^{-1} = (a^{2^{n-1} - 1})^2``, with ``\\beta_k = a^{2^k - 1}`` built along the
binary expansion of ``n - 1`` by ``\\beta_{2k} = \\beta_k^{2^k}\\,\\beta_k`` and
``\\beta_{2k+1} = \\beta_{2k}^2\\,a``. The Frobenius powers ``x \\mapsto x^{2^k}`` are
``\\mathbb{F}_2``-linear in any basis and applied as byte tables, built once per field at
compile time; so the cost is about ``2\\log_2 n`` table maps and products, for nimbers and
polynomial bases alike.
"""
struct ItohTsujii <: InvStrategy end

"""
    Euclid()

The extended Euclidean algorithm on the modulus ``f`` and ``a`` in a polynomial basis
``\\mathbb{F}_2[x]/(f)``, one leading bit cleared per step (about ``2n`` steps). For
[`PolyElement`](@ref) directly; for nimbers from GF(2^16) up through the polynomial basis of
[`CLMul`](@ref) (change of basis by byte tables), below that as [`MulTable`](@ref).
"""
struct Euclid <: InvStrategy end

@stable default_mode = "error" begin
    # Inverse of a ≠ 0 modulo f = x^N + low (irreducible), coefficients as bits of T.
    # Invariant s_i · a ≡ r_i (mod f). The first division step removes the x^N of f, which need
    # not fit in T: (x^N + low) - a · x^(N - deg a) has no x^N term.
    @inline function euclid_inv_bits(a::T, ::Val{N}, low::T) where {T <: Unsigned, N}
        isone(a) && return one(T)
        top(v) = 8 * sizeof(T) - 1 - leading_zeros(v)
        mask = N == 8 * sizeof(T) ? typemax(T) : (one(T) << N) - one(T)
        sh = N - top(a)
        r0, r1 = (low ⊻ (a << sh)) & mask, a
        s0, s1 = one(T) << sh, one(T)
        while true
            d1 = top(r1)
            d0 = top(r0)
            while d0 >= d1
                k = d0 - d1
                r0 ⊻= r1 << k
                s0 ⊻= s1 << k
                d0 = top(r0)
            end
            iszero(r0) && throw(ArgumentError("Euclid: the modulus is not irreducible"))
            r0, r1 = r1, r0
            s0, s1 = s1, s0
            isone(r1) && return s1
        end
    end

    function inverse(::Fermat, a::F) where {F <: BinaryFieldElement}
        iszero(a) && throw(DivideError())
        return Base.power_by_squaring(a, multiplicative_order(F) - one(storagetype(F)))
    end

    function inverse(::ItohTsujii, a::F) where {F <: BinaryFieldElement}
        iszero(a) && throw(DivideError())
        return itoh_tsujii(a)
    end

    function inverse(::Euclid, a::P) where {N, T, F, P <: PolyElement{N, T, F}}
        iszero(a) && throw(DivideError())
        return unsafe_frombits(P, euclid_inv_bits(bits(a), Val(N), F))
    end

    function inverse(::Euclid, a::Nimber{K, T}) where {K, T}
        iszero(a) && throw(DivideError())
        return unsafe_frombits(Nimber{K, T}, nimber_euclid_bits(bits(a), Val(K)))
    end

    # The polynomial bases of nimber_fast.jl exist from GF(2^16) up.
    @inline nimber_euclid_bits(a::T, v::TableLevel) where {T} = nim_inv_bits(MulTable(), a, v)
    @inline nimber_euclid_bits(a::T, ::Val{K}) where {T, K} =
        from_poly(euclid_inv_bits(to_poly(a), Val(1 << K), poly_modulus_bits(T)))
end

poly_modulus_bits(::Type{T}) where {T <: Unsigned} =
    foldl((acc, e) -> acc | (one(T) << e), poly_modulus(T); init = zero(T))

# --- Itoh–Tsujii ------------------------------------------------------------------------------

# Byte tables of the Frobenius power x ↦ x^(2^k) on F (images of the basis vectors by k squarings).
function frobenius_table(::Type{F}, k::Int) where {F <: BinaryFieldElement}
    T = storagetype(F)
    img = zeros(T, 8 * sizeof(T))
    for i in 0:(degree(F) - 1)
        y = unsafe_frombits(F, one(T) << i)
        for _ in 1:k
            y = y * y
        end
        img[i + 1] = bits(y)
    end
    return byte_tables(img)
end

# The chain for n: a list of steps (k, times_a): β ← β^(2^k) · (times_a ? a : β), with the table
# of x ↦ x^(2^k) for each step, ending with a squaring.
function itoh_tsujii_plan(::Type{F}) where {F <: BinaryFieldElement}
    n = degree(F)
    e = n - 1
    steps = Tuple{Matrix{storagetype(F)}, Bool}[]
    tables = Dict{Int, Matrix{storagetype(F)}}()
    tab(k) = get!(() -> frobenius_table(F, k), tables, k)
    k = 1                                          # β = a = a^(2^1 - 1)
    for i in (8 * sizeof(Int) - leading_zeros(e) - 2):-1:0
        push!(steps, (tab(k), false))              # β_{2k} = β_k^(2^k) β_k
        k *= 2
        if isodd(e >> i)
            push!(steps, (tab(1), true))           # β_{k+1} = β_k^2 a
            k += 1
        end
    end
    return steps, tab(1)
end

# Unrolled at compile time, with the tables as constants of the generated code.
@generated function itoh_tsujii(a::F) where {F <: BinaryFieldElement}
    degree(F) == 1 && return :(a)                  # GF(2): a = 1
    steps, sq = itoh_tsujii_plan(F)
    body = Expr(:block, :(β = a))
    for (t, times_a) in steps
        other = times_a ? :a : :β
        push!(body.args, :(β = unsafe_frombits($F, apply_bytes($t, bits(β))) * $other))
    end
    push!(body.args, :(return unsafe_frombits($F, apply_bytes($sq, bits(β)))))
    return body
end

# --- Defaults ---------------------------------------------------------------------------------

# Polynomial bases: the tables of polyfield.jl up to degree 16 (MulTable to 8, LogTable to 16;
# 10-50x ItohTsujii, polyfield.md, "Table strategies"), above that ItohTsujii, the best
# throughput at every degree measured (2–3× Euclid; inversion.md, "Measurements").
# Nimbers keep their norm-recursion defaults (nimber.jl, nimber_fast.jl), faster than all three.
default_inv_strategy(::Type{<:PolyElement{N}}) where {N} =
    N <= POLY_MULTABLE_MAX_DEGREE ? MulTable() : N <= POLY_LOGTABLE_MAX_DEGREE ? LogTable() :
    ItohTsujii()

@stable default_mode = "error" begin
    Base.inv(a::PolyElement) = inverse(default_inv_strategy(typeof(a)), a)
end
