# J1a: pseudo-Conway fields for the 15 degrees n ≤ 128 missing from Lübeck's table, defined from
# On_2 (option B, src/polyfield.md, "Pseudo-Conway fields").
#
# Oracles: Rabin's irreducibility test (poly_field); the prime divisors of 2^n - 1 (data, checked
# here to exhaust 2^n - 1 and to pass a Miller–Rabin test) for primitivity; the Conway polynomials
# C_m evaluated directly (Conway compatibility, independent of On_2); the defining rule recomputed
# in nim_field(n) (least-rank primitive β, least admissible k); the Horner embedding for the
# embeddings.

using FiniteFieldArithmetic
using FiniteFieldArithmetic: bits, field_modulus, embed_horner, conway_exponent,
    PSEUDO_CONWAY_TABLE, PSEUDO_CONWAY_PRIMES
using Random
using Test

const MISSING = [93, 94, 99, 104, 105, 106, 111, 112, 116, 117, 118, 122, 123, 124, 128]
rng = Xoshiro(51)
ord(n) = big(2)^n - 1
pw(x, e::BigInt) = x^UInt128(e)

# Miller–Rabin with 24 fixed bases: probabilistic for the large factors (error < 4^-24 each)
function probably_prime(p::BigInt)
    p < 2 && return false
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
        p == q && return true
        p % q == 0 && return false
    end
    d, s = p - 1, 0
    while iseven(d)
        d >>= 1; s += 1
    end
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89)
        a < p || continue                                   # p itself (or above) is no witness
        x = powermod(big(a), d, p)
        (x == 1 || x == p - 1) && continue
        any(_ -> (x = powermod(x, 2, p); x == p - 1), 1:(s - 1)) || return false
    end
    return true
end

primitive(x, n) = !iszero(x) && all(p -> !isone(pw(x, ord(n) ÷ p)), PSEUDO_CONWAY_PRIMES[n])

@testset "degrees and types" begin
    @test pseudo_conway_degrees() == MISSING
    @test sort(vcat(conway_degrees(), pseudo_conway_degrees())) == 1:128
    for n in MISSING
        P = pseudo_conway_field(n)
        @test P === pseudo_conway_field(Val(n))
        @test is_pseudo_conway(P) && !is_conway(P)
        @test degree(P) == n
        @test_throws ArgumentError conway_field(n)
    end
    @test !is_pseudo_conway(conway_field(8)) && !is_pseudo_conway(GF256_AES) && !is_pseudo_conway(GF256)
    @test_throws ArgumentError pseudo_conway_field(8)
    @test_throws ArgumentError pseudo_conway_field(129)
end

@testset "irreducible, primitive, Conway-compatible" begin
    for n in MISSING
        P = pseudo_conway_field(n)
        @test poly_field(n, field_modulus(P)) === P                  # Rabin's test passes
        # the prime list is complete (and each entry is prime)
        N = ord(n)
        for p in PSEUDO_CONWAY_PRIMES[n]
            @test probably_prime(p)
            while N % p == 0
                N ÷= p
            end
        end
        @test N == 1
        α = conway_generator(P)
        @test isone(pw(α, ord(n)))
        @test primitive(α, n)
        # compatibility with C_m for every m | n, evaluated directly in P
        for m in conway_degrees()
            (m < n && n % m == 0) || continue
            r = α^conway_exponent(m, n)
            low = UInt128(field_modulus(conway_field(m)))
            @test iszero(r^m + sum((isodd(low >> i) ? r^i : zero(P)) for i in 0:(m - 1)))
        end
    end
end

@testset "the rule in On_2" begin
    maxdivs(n) = [m for m in 1:(n - 1) if n % m == 0 &&
                  !any(d -> m < d < n && n % d == 0 && d % m == 0, 1:(n - 1))]
    for (n, low, rho, βr, k) in PSEUDO_CONWAY_TABLE
        F = nim_field(n)
        ρ = embed(F, conway_generator(pseudo_conway_field(n)))
        @test bits(ρ) == rho
        β = F(βr)
        @test primitive(β, n)
        # β is the least-rank primitive element: the ranks below 2^(2^j) (2^j the largest power of
        # two dividing n, below n) are the nimber subfield GF(2^(2^j)), an initial segment of
        # On_2, so not primitive (checked on samples); above, every rank up to β is checked
        j = trailing_zeros(n == 128 ? 64 : n)
        lo = UInt128(1) << (1 << j)
        N2 = FiniteFieldArithmetic.NIMBER_LEVELS[j + 1]                 # GF(2^(2^j)), level j
        for r in (UInt128(1), lo - 1, rand(rng, UInt128(1):(lo - 1)))
            @test F(r) == embed(F, N2(r))
        end
        @test βr >= lo
        @test all(r -> !primitive(F(r), n), lo:(βr - 1))
        @test pw(β, k) == ρ
        # ρ = β^k satisfies the norm conditions, and no smaller admissible k does: the k' with the
        # same norms are k' ≡ k (mod M), M = lcm(2^m - 1, m maximal), and those below k are not
        # prime to 2^n - 1
        M = foldl(lcm, (ord(m) for m in maxdivs(n)); init = big(1))
        for m in conway_degrees()
            (m < n && n % m == 0) || continue
            @test pw(ρ, ord(n) ÷ ord(m)) == embed(F, conway_generator(conway_field(m)))
        end
        @test all(t -> gcd(k - t * M, ord(n)) != 1, 1:((k - 1) ÷ M))
        @test gcd(k, ord(n)) == 1
    end
end

@testset "arithmetic and embeddings" begin
    for n in MISSING
        P, F = pseudo_conway_field(n), nim_field(n)
        for _ in 1:8
            x, y = rand(rng, P), rand(rng, P)
            iszero(x) || @test x * inv(x) == one(P)
            @test embed(F, x * y) == embed(F, x) * embed(F, y)           # the isomorphism with On_2
            @test embed(F, x + y) == embed(F, x) + embed(F, y)
            @test embed(P, embed(F, x)) == x
            u = rand(rng, F)
            @test embed(F, embed(P, u)) == u
        end
        # Conway (and nimber, Nim) sources: through On_2 = the definition (Horner)
        for m in conway_degrees()
            (m < n && n % m == 0) || continue
            C = conway_field(m)
            @test embed(P, conway_generator(C)) == embed_horner(P, conway_generator(C))
            for _ in 1:3
                x = rand(rng, C)
                @test embed(P, x) == embed_horner(P, x)
                @test embed(F, embed(P, x)) == embed(F, x)
                u = rand(rng, nim_field(m))
                @test embed(P, u) == embed(P, embed(C, u))
            end
        end
    end
    # degree 128: the isomorphism with the nimbers GF(2^128)
    P = pseudo_conway_field(128)
    for _ in 1:20
        x, y = rand(rng, P), rand(rng, P)
        @test embed(GF2_128, x * y) == embed(GF2_128, x) * embed(GF2_128, y)
        @test embed(P, embed(GF2_128, x)) == x
        u = rand(rng, GF2_64)
        @test embed(P, u) == embed(P, embed(conway_field(64), u))
        @test embed(GF2_128, embed(P, u)) == GF2_128(u)
    end
    @test_throws ArgumentError embed(pseudo_conway_field(93), conway_field(5)(1))
    @test_throws ArgumentError embed(GF2_128_GHASH, pseudo_conway_field(128)(1))  # GHASH: not in the system
end

@testset "type stability" begin
    for n in (93, 122, 128)
        P = pseudo_conway_field(Val(n))
        x, y = P(5), P(3)
        @test (@inferred x * y) isa P
        @test (@inferred inv(x)) isa P
        @test (@inferred embed(nim_field(Val(n)), x)) isa nim_field(n)
        @test (@inferred embed(P, nim_field(Val(n))(5))) isa P
    end
    @test (@inferred embed(pseudo_conway_field(Val(124)), conway_field(Val(62))(5))) isa pseudo_conway_field(124)
end
