# Pseudo-Conway polynomials from On_2 (option B, approved 2026-11-21) for the 15 degrees n ≤ 128
# missing from Lübeck's table, written to julia/FiniteFieldArithmetic.jl/src/pseudo_conway_table.jl.
#
# Rule, in GF(2^n) ⊂ On_2 (rank encoding, ADR-0005), with ρ_m the image of the Conway generator α_m
# for the table degrees m (src/nim_conway_roots.jl; every proper divisor of a missing degree is a
# table degree):
#   1. β = the primitive element of least rank;
#   2. k = the least k ≥ 1 with gcd(k, 2^n - 1) = 1 and N_m(β^k) = ρ_m for every maximal proper
#      divisor m of n, where N_m(x) = x^((2^n-1)/(2^m-1)) (then for every m | n, by transitivity of
#      the norms and the compatibility of the ρ_m);
#   3. ρ_n = β^k, and the pseudo-Conway polynomial P_n is its minimal polynomial.
# N_m(β) is primitive in GF(2^m), so N_m(β) = ρ_m^ℓ_m with ℓ_m a unit mod 2^m - 1, and the condition
# is k ≡ ℓ_m^(-1) (mod 2^m - 1). The ℓ_m are discrete logarithms in conway_field(m) (Pohlig–Hellman;
# baby-step giant-step, Pollard rho for large prime factors); the congruences are combined by CRT.
#
# Needs data/mersenne_factors.txt (mersenne_factors.py).
# Uses only the Conway and rank-encoded fields of the package, not its pseudo-Conway table (which
# the package loads, and this script overwrites).
# Run: nix develop .#julia -c julia --project=julia/FiniteFieldArithmetic.jl research/nimber_closure/pseudo_conway.jl

using FiniteFieldArithmetic
using FiniteFieldArithmetic: bits, unsafe_frombits, storagetype
using Random

const MISSING = [93, 94, 99, 104, 105, 106, 111, 112, 116, 117, 118, 122, 123, 124, 128]

const FACTORS = let d = Dict{Int, Vector{BigInt}}()
    for line in eachline(joinpath(@__DIR__, "data", "mersenne_factors.txt"))
        startswith(line, "#") && continue
        n, fs = split(line, ":")
        d[parse(Int, n)] = parse.(BigInt, split(fs))
    end
    d
end
primes_of(n) = unique(FACTORS[n])
order(n) = big(2)^n - 1

say(xs...) = (println(stderr, xs...); flush(stderr))

pow(x, e::BigInt) = x^UInt128(e)                     # e < 2^128 throughout

is_primitive(x, n) = !iszero(x) && all(p -> !isone(pow(x, order(n) ÷ p)), primes_of(n))

# --- discrete logarithms -------------------------------------------------------------------------

# log_γ(η) for γ of prime order p
function dlog_prime(γ, η, p::BigInt, rng)
    isone(η) && return big(0)
    p < big(2)^42 ? bsgs(γ, η, p) : rho(γ, η, p, rng)
end

function bsgs(γ, η, p::BigInt)
    s = Int(isqrt(p)) + 1
    table = Dict{typeof(bits(γ)), Int}()
    x = one(γ)
    for j in 0:(s - 1)
        get!(table, bits(x), j)
        x *= γ
    end
    giant = inv(pow(γ, big(s)))
    y = η
    for i in 0:s
        j = get(table, bits(y), -1)
        j >= 0 && return mod(big(i) * s + j, p)
        y *= giant
    end
    error("bsgs: no logarithm")
end

# Pollard rho with Teske's r-adding walk (r = 32) and Brent's cycle detection.
function rho(γ, η, p::BigInt, rng)
    q = UInt64(p)
    addq(a, b) = (s = a + b; s >= q ? s - q : s)
    while true
        A = [rand(rng, UInt64(0):(q - 1)) for _ in 1:32]
        B = [rand(rng, UInt64(0):(q - 1)) for _ in 1:32]
        M = [pow(γ, big(A[i])) * pow(η, big(B[i])) for i in 1:32]
        idx(x) = Int((UInt64(bits(x) % UInt64) * 0x9e3779b97f4a7c15) >> 59) + 1
        a0, b0 = rand(rng, UInt64(0):(q - 1)), rand(rng, UInt64(0):(q - 1))
        x = pow(γ, big(a0)) * pow(η, big(b0))
        a, b = a0, b0
        tx, ta, tb = x, a, b                          # tortoise
        power, lam = UInt64(1), UInt64(0)
        steps = 0
        while true
            i = idx(x)
            x *= M[i]; a = addq(a, A[i]); b = addq(b, B[i])
            lam += 1; steps += 1
            steps & (2^30 - 1) == 0 && say("    rho: p = $p, $steps steps so far")
            x == tx && break
            if lam == power
                tx, ta, tb = x, a, b
                power <<= 1; lam = 0
            end
        end
        # γ^ta η^tb = γ^a η^b  ⇒  log η = (ta - a)/(b - tb)
        db = mod(big(b) - big(tb), p)
        iszero(db) && continue
        L = mod((big(ta) - big(a)) * invmod(db, p), p)
        pow(γ, L) == η || error("rho: wrong logarithm")
        say("    rho: p = $p, $steps steps")
        return L
    end
end

# log_g(h) for g of order N = 2^m - 1 (Pohlig–Hellman over the factorisation of N)
function dlog(g, h, m, rng)
    N = order(m)
    rs, ms = BigInt[], BigInt[]
    for p in primes_of(m)
        e = count(==(p), FACTORS[m])
        pe = p^e
        gp, hp = pow(g, N ÷ pe), pow(h, N ÷ pe)
        γ = pow(gp, pe ÷ p)                           # order p
        x = big(0)
        for k in 0:(e - 1)
            η = pow(hp * inv(pow(gp, x)), pe ÷ p^(k + 1))
            x += dlog_prime(γ, η, p, rng) * p^k
        end
        push!(rs, x); push!(ms, pe)
    end
    L = crt(rs, ms)
    pow(g, L) == h || error("dlog: wrong logarithm")
    return L
end

# x ≡ r_i (mod m_i), moduli not necessarily coprime; returns (x, lcm)
function crt2(r1, m1, r2, m2)
    g = gcd(m1, m2)
    mod(r2 - r1, g) == 0 || error("crt: inconsistent congruences")
    l = m1 ÷ g * m2
    t = mod((r2 - r1) ÷ g * invmod(m1 ÷ g, m2 ÷ g), m2 ÷ g)
    return mod(r1 + m1 * t, l), l
end
crt(rs, ms) = first(foldl((acc, rm) -> crt2(acc..., rm...), zip(rs, ms); init = (big(0), big(1))))

# --- the construction ----------------------------------------------------------------------------

maximal_divisors(n) = [m for m in 1:(n - 1) if n % m == 0 && !any(d -> d > m && d < n && n % d == 0 && d % m == 0, 1:(n - 1))]

# x ∈ GF(2^n) lying in GF(2^m), m | n, as an element of conway_field(m)
to_conway(x, m) = (r = reduce_field(x); embed(conway_field(m), r))

function construct(n, rng)
    F = nim_field(n)
    # The ranks below 2^(2^j), 2^j the largest power of two dividing n (and < n), are the nimber
    # subfield GF(2^(2^j)), an initial segment of On_2: no primitive element there, so the search
    # for the least-rank primitive element starts above (for n = 128 at 2^64).
    βr = UInt128(1) << (1 << trailing_zeros(n == 128 ? 64 : n))
    while !is_primitive(F(βr), n)
        βr += 1
    end
    β = F(βr)
    rs, ms = BigInt[], BigInt[]
    for m in maximal_divisors(n)
        y = to_conway(pow(β, order(n) ÷ order(m)), m)
        ℓ = dlog(conway_generator(conway_field(m)), y, m, rng)
        push!(rs, invmod(ℓ, order(m))); push!(ms, order(m))
    end
    k0, M = foldl((acc, rm) -> crt2(acc..., rm...), zip(rs, ms); init = (big(0), big(1)))
    k = iszero(k0) ? M : k0
    while gcd(k, order(n)) != 1
        k += M
    end
    ρ = pow(β, k)
    # checks: primitive; N_m(ρ) = ρ_m for every table divisor m
    @assert is_primitive(ρ, n)
    for m in conway_degrees()
        (m < n && n % m == 0) || continue
        @assert pow(ρ, order(n) ÷ order(m)) == embed(F, conway_generator(conway_field(m)))
    end
    # minimal polynomial: ∏ (X - ρ^(2^i)), coefficients in GF(2)
    poly = [one(F)]                                  # lowest first
    c = ρ
    for _ in 1:n
        new = vcat([zero(F)], poly)                  # X * poly
        for i in eachindex(poly)
            new[i] += c * poly[i]
        end
        poly = new
        c = c * c
    end
    @assert c == ρ
    @assert all(x -> iszero(x) || isone(x), poly) && isone(poly[end])
    low = foldl((acc, i) -> isone(poly[i + 1]) ? acc | (UInt128(1) << i) : acc, 0:(n - 1); init = UInt128(0))
    return (; low, rho = UInt128(bits(ρ)), beta = βr, k, M)
end

function main()
rng = Xoshiro(20261121)
res = Dict{Int, Any}()
for n in MISSING
    t = @elapsed res[n] = construct(n, rng)
    r = res[n]
    say("n = $n: β = rank $(r.beta), k = $(r.k) (class mod $(r.M)), low = 0x",
            string(r.low; base = 16), ", $(round(t; digits = 1)) s")
end

out = joinpath(@__DIR__, "..", "..", "julia", "FiniteFieldArithmetic.jl", "src", "pseudo_conway_table.jl")
open(out, "w") do io
    println(io, """
    # Generated by research/nimber_closure/pseudo_conway.jl. Do not edit by hand.
    #
    # Pseudo-Conway polynomials P_n for the degrees n ≤ 128 missing from Lübeck's table, defined from
    # On_2 (src/polyfield.md, "Pseudo-Conway fields"): in GF(2^n) ⊂ On_2, β the primitive element of
    # least rank, k the least k ≥ 1 with gcd(k, 2^n - 1) = 1 and β^(k (2^n-1)/(2^m-1)) = ρ_m for every
    # m | n, ρ_n = β^k, P_n its minimal polynomial. Columns: n, the bits of P_n - x^n, the rank of ρ_n,
    # the rank of β, k. PSEUDO_CONWAY_PRIMES[n]: the distinct primes dividing 2^n - 1 (GNU factor,
    # checked with sympy.isprime by research/nimber_closure/mersenne_factors.py).
    """)
    println(io, "const PSEUDO_CONWAY_TABLE = (")
    for n in MISSING
        r = res[n]
        println(io, "    ($n, 0x", string(r.low; base = 16, pad = 32), ", 0x", string(r.rho; base = 16, pad = 32),
                ", 0x", string(r.beta; base = 16, pad = 32), ", big\"$(r.k)\"),")
    end
    println(io, ")")
    println(io)
    println(io, "const PSEUDO_CONWAY_PRIMES = Dict{Int, Vector{BigInt}}(")
    for n in MISSING
        println(io, "    $n => BigInt[", join(("big\"$p\"" for p in primes_of(n)), ", "), "],")
    end
    println(io, ")")
end
say("wrote ", out)
end

abspath(PROGRAM_FILE) == @__FILE__() && main()
