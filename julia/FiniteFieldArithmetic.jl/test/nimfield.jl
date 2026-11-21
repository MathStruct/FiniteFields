# J10: the rank-encoded fields GF(2^n) ⊂ Conway's On_2 for every n ≤ 128 (ADR-0005), `Nim{N, T}`,
# with `Nimber` for n = 2^k.
#
# Oracles: the field axioms; the Frobenius (x^(2^n) = x, and the smallest d with x^(2^d) = x for
# minimal_degree); the research data of R1 (research/nimber_closure/data/rank/n_*.txt, computed in
# On_2 and checked there: rank = ordinal position by brute force for small fields), compared
# directly when the files are present; known values (GF(8) ⊂ GF(64): ranks 2, 4 ↦ 28, 40).

using FiniteFieldArithmetic
using FiniteFieldArithmetic: bits, storagetype
using Random
using Test

const NONPOW2 = [n for n in 1:128 if !ispow2(n)]
const RESEARCH = joinpath(@__DIR__, "..", "..", "..", "research", "nimber_closure", "data", "rank")
mask(n) = n == 128 ? typemax(UInt128) : (UInt128(1) << n) - 1

@testset "types" begin
    for (k, N) in enumerate((GF2, GF4, GF16, GF256, GF2_16, GF2_32, GF2_64, GF2_128))
        @test nim_field(degree(N)) === N                   # n = 2^k: the nimbers themselves
    end
    for n in NONPOW2
        F = nim_field(n)
        @test F <: Nim
        @test degree(F) == n
        @test storagetype(F) == (n <= 8 ? UInt8 : n <= 16 ? UInt16 : n <= 32 ? UInt32 :
                                 n <= 64 ? UInt64 : UInt128)
        @test nim_field(Val(n)) === F
    end
    @test_throws ArgumentError nim_field(0)
    @test_throws ArgumentError nim_field(129)
    @test_throws ArgumentError nim_field(3)(8)                  # rank 8 is not below 2^3
    @test nim_field(3)(5) isa nim_field(3)
end

rng = Xoshiro(41)
sample(F, k) = degree(F) <= 8 ? collect(elements(F)) : vcat([rand(rng, F) for _ in 1:k], [zero(F), one(F)])

@testset "field axioms and Frobenius" begin
    for n in NONPOW2
        F = nim_field(n)
        xs = sample(F, 40)
        for x in xs
            y, z = rand(rng, xs), rand(rng, xs)
            @test x * y == y * x
            @test (x * y) * z == x * (y * z)
            @test x * (y + z) == x * y + x * z
            @test one(F) * x == x
            if !iszero(x)
                @test isone(x * inv(x))
                @test y / x * x == y
            end
            @test x^(big(2)^n) == x                                 # x ∈ GF(2^n)
        end
        @test_throws DivideError inv(zero(F))
        @test bits(one(F)) == 1                                       # 1 has rank 1
    end
end

@testset "exhaustive small fields" begin
    for n in (3, 5, 6, 7, 9, 10, 11, 12)
        F = nim_field(n)
        xs = collect(elements(F))
        for x in xs[2:end]
            @test count(y -> isone(x * y), xs) == 1                   # unique inverse
        end
        # the multiplicative group is cyclic of order 2^n - 1
        q = 2^n - 1
        @test any(g -> all(p -> !isone(g^(q ÷ p)), [p for p in 2:q if q % p == 0 && all(p % r != 0 for r in 2:isqrt(p))]),
                  xs[2:end])
    end
end

@testset "inclusions" begin
    # GF(8) ⊂ GF(64): known from the hand computation in On_2 (gf8_as_ordinals.jl)
    @test embed(nim_field(6), nim_field(3)(2)) == nim_field(6)(28)
    @test embed(nim_field(6), nim_field(3)(4)) == nim_field(6)(40)
    # GF(4) = ranks 0…3 is the bottom of every field of even degree (an initial segment)
    for n in (6, 10, 12, 14, 30, 126)
        for v in 0:3
            @test embed(nim_field(n), GF4(v)) == nim_field(n)(v)
        end
    end
    for n in NONPOW2, m in 1:(n - 1)
        n % m == 0 || continue
        Fm, Fn = nim_field(m), nim_field(n)
        for _ in 1:8
            x, y = rand(rng, Fm), rand(rng, Fm)
            @test embed(Fn, x * y) == embed(Fn, x) * embed(Fn, y)
            @test embed(Fn, x + y) == embed(Fn, x) + embed(Fn, y)
        end
        @test embed(Fn, one(Fm)) == one(Fn)
        for l in 1:(m - 1)                                             # l | m | n: compatible
            m % l == 0 || continue
            x = rand(rng, nim_field(l))
            @test embed(Fn, embed(Fm, x)) == embed(Fn, x)
        end
    end
    @test_throws ArgumentError embed(nim_field(6), nim_field(5)(1))   # 5 ∤ 6
    @test embed(nim_field(12), nim_field(12)(7)) === nim_field(12)(7)
end

@testset "equality, hashing and promotion across fields" begin
    a = nim_field(3)(5)
    b = embed(nim_field(6), a)
    @test a == b && b == a
    @test hash(a) == hash(b)
    @test nim_field(3)(1) == nim_field(43)(1) == GF2(1) == GF256(1)  # 1 everywhere
    @test hash(nim_field(43)(1)) == hash(GF2(1))
    c = nim_field(12)(3)                                               # rank 3 = nimber 3 ∈ GF(4)
    @test c == GF4(3) && hash(c) == hash(GF4(3))
    @test nim_field(3)(2) != nim_field(5)(2)                           # GF(8) ∩ GF(32) = GF(2)
    @test length(Set([a, b, embed(nim_field(12), a), embed(nim_field(126), a)])) == 1
    # mixed arithmetic promotes to the field of degree lcm(m, n) when it is ≤ 128
    @test nim_field(3)(2) * nim_field(6)(5) isa nim_field(6)
    @test nim_field(3)(2) + nim_field(5)(3) isa nim_field(15)
    @test nim_field(3)(2) * GF16(7) isa nim_field(12)
    @test nim_field(3)(2) * GF16(7) == embed(nim_field(12), nim_field(3)(2)) * embed(nim_field(12), GF16(7))
    @test nim_field(6)(9) * GF4(2) isa nim_field(6)
    @test_throws Exception nim_field(3)(2) * nim_field(43)(2)          # lcm 129 > 128
    @test Set([GF2(1), nim_field(5)(1)]) == Set([GF2(1)])
end

@testset "smallest field of an element (J9b for the default representation)" begin
    frob_degree(x) = (y = x * x; d = 1; while y != x; y = y * y; d += 1; end; d)
    for n in (6, 12, 15, 30, 60, 105, 126)
        F = nim_field(n)
        for x in sample(F, 60)
            d = minimal_degree(x)
            @test d == frob_degree(x)
            r = reduce_field(x)
            @test degree(typeof(r)) == d
            @test r == x
            @test typeof(r) === nim_field(d)
        end
    end
    @test reduce_field(nim_field(12)(3)) === GF4(3)
    @test minimal_degree(nim_field(6)(28)) == 3
end

@testset "agrees with the research data" begin
    if isdir(RESEARCH)
        for n in NONPOW2
            d = Dict{String, String}()
            for line in eachline(joinpath(RESEARCH, "n_$n.txt"))
                k, v = split(line, '\t'); d[k] = v
            end
            F = nim_field(n)
            g = F(parse(UInt128, d["g"]))
            C = parse.(UInt128, split(d["C"], ','))
            @test all(bits(g^(i - 1)) == C[i] for i in 1:n)         # powers of the internal generator
            for (k, v) in d
                startswith(k, "embed") || continue
                m = parse(Int, split(k)[2])
                cols = parse.(UInt128, split(v, ','))
                Fm = nim_field(m)
                @test all(bits(embed(F, Fm(UInt128(1) << (i - 1)))) == cols[i] for i in 1:m)
            end
        end
    else
        @info "research data not found; skipped"
    end
end

@testset "Conway fields: the roots α_n in On_2" begin
    # For every Conway degree n, the image of α_n in GF(2^n) ⊂ On_2 is a root of C_n, compatible
    # with the image of α_m for every m | n, and of least rank among the compatible roots; for
    # n = 2^k it is the root r_k of polyfield.md.
    image(n) = embed(nim_field(n), conway_generator(conway_field(n)))
    for n in conway_degrees()
        F = nim_field(n)
        r = image(n)
        low = UInt128(FiniteFieldArithmetic.field_modulus(conway_field(n)))
        @test iszero(r^n + sum((isodd(low >> i) ? r^i : zero(F)) for i in 0:(n - 1)))   # C_n(r) = 0
        divs = [m for m in conway_degrees() if m < n && n % m == 0]
        compatible(s) = all(m -> s^FiniteFieldArithmetic.conway_exponent(m, n) == embed(F, image(m)), divs)
        @test compatible(r)
        orbit = accumulate((s, _) -> s * s, 1:n; init = r)            # r^2, r^4, …, r^(2^n) = r
        @test last(orbit) == r
        @test all(s -> !compatible(s) || bits(s) >= bits(r), orbit)
        if ispow2(n)
            @test bits(r) == bits(FiniteFieldArithmetic.CONWAY_NIMBER_ROOTS[trailing_zeros(n) + 1])
        end
    end
end

@testset "Conway fields: embed to and from nim_field" begin
    conway_nonpow2 = [n for n in conway_degrees() if !ispow2(n)]
    # isomorphisms conway_field(n) ≅ nim_field(n): ring homomorphisms, mutually inverse
    for n in conway_nonpow2
        C, F = conway_field(n), nim_field(n)
        for _ in 1:8
            x, y = rand(rng, C), rand(rng, C)
            @test embed(F, x * y) == embed(F, x) * embed(F, y)
            @test embed(F, x + y) == embed(F, x) + embed(F, y)
            @test embed(C, embed(F, x)) == x
            u = rand(rng, F)
            @test embed(F, embed(C, u)) == u
        end
        @test embed(F, one(C)) == one(F)
        @test embed(F, zero(C)) == zero(F)
        @test embed(C, one(F)) == one(C)
    end
    for n in filter(<=(12), conway_nonpow2)                            # bijective
        @test length(Set(bits(embed(nim_field(n), x)) for x in elements(conway_field(n)))) == 2^n
    end
    # the squares commute: Conway embedding, then the isomorphism = the isomorphism, then the
    # inclusion of On_2 (for all table pairs m | n, sources Conway, Nim and Nimber)
    for n in conway_degrees(), m in conway_degrees()
        (m < n && n % m == 0) || continue
        Cm, Cn, Fm, Fn = conway_field(m), conway_field(n), nim_field(m), nim_field(n)
        for _ in 1:(n <= 72 ? 4 : 2)
            x = rand(rng, Cm)
            @test embed(Fn, embed(Cn, x)) == embed(Fn, x)                # Conway → Nim/Nimber
            @test embed(Fn, x) == embed(Fn, embed(Fm, x))                # through the subfield
            u = rand(rng, Fm)
            @test embed(Cn, u) == embed(Cn, embed(Cm, u))                # Nim/Nimber → Conway
        end
    end
    # a Conway source needs only its own α_m: GF(2^31) and GF(2^3) into GF(2^93) (no C_93)
    for m in (3, 31)
        x, y = rand(rng, conway_field(m)), rand(rng, conway_field(m))
        F = nim_field(93)
        @test embed(F, x * y) == embed(F, x) * embed(F, y)
        @test embed(F, x) == embed(F, embed(nim_field(m), x))
    end
    @test embed(nim_field(12), conway_field(4)(0x2)) == embed(nim_field(12), embed(GF16, conway_field(4)(0x2)))
    # not defined: degrees that do not divide, fields outside the compatible system
    @test_throws ArgumentError embed(nim_field(12), conway_field(5)(1))
    @test_throws ArgumentError embed(conway_field(5), nim_field(3)(1))
    @test_throws ArgumentError embed(nim_field(24), GF256_AES(1))
    @test_throws ArgumentError embed(nim_field(3), poly_field(3, 0x5)(1))
    @test_throws ArgumentError embed(poly_field(3, 0x5), nim_field(3)(1))
    @test_throws ArgumentError embed(conway_field(3), nim_field(93)(1))
    # no implicit equality or promotion between the representations (J1a decision (b))
    @test conway_field(3)(1) != nim_field(3)(1)
    for (m, n) in ((3, 12), (12, 12), (21, 126), (8, 24))
        x = conway_field(m)(5)
        @test (@inferred embed(nim_field(Val(n)), x)) isa nim_field(n)
        @test (@inferred embed(conway_field(Val(n)), nim_field(Val(m))(5))) isa conway_field(n)
    end
end

@testset "printing and type stability" begin
    @test string(nim_field(3)(5)) == "0x5"
    @test repr(nim_field(3)(5)) == "0x5 ∈ GF(2^3)"
    @test string(nim_field(127)(1)) == "0x" * "0"^31 * "1"
    for n in (3, 12, 33, 107, 127)
        x, y = nim_field(n)(5), nim_field(n)(3)
        @test (@inferred x * y) isa nim_field(n)
        @test (@inferred inv(x)) isa nim_field(n)
        @test (@inferred x / y) isa nim_field(n)
        @test (@inferred minimal_degree(x)) isa Int
    end
end
