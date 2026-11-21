# J1a: polynomial-basis fields GF(2)[x]/(f), the Conway fields among them, the AES and GHASH
# fields, embeddings between Conway fields and the isomorphisms between Conway and nimber fields.
#
# Oracles, independent of the implementation: polynomials over GF(2) as BigInt bit patterns
# (bit i = coefficient of x^i) with schoolbook arithmetic; irreducibility by Rabin's test;
# primitivity from the factorisation of 2^n - 1 (trial division, Pollard's rho, Miller–Rabin).

using FiniteFieldArithmetic
using FiniteFieldArithmetic: bits, storagetype, CONWAY_TABLE, conway_degrees
using Random
using Test

# --- Polynomials over GF(2) as BigInt bit patterns --------------------------------------------

pdeg(a::BigInt) = iszero(a) ? -1 : ndigits(a; base = 2) - 1
function pmul(a::BigInt, b::BigInt)
    r = big(0)
    i = 0
    while !iszero(b)
        isodd(b) && (r = xor(r, a << i))
        b >>= 1
        i += 1
    end
    return r
end
function pmod(a::BigInt, f::BigInt)
    d = pdeg(f)
    while pdeg(a) >= d
        a = xor(a, f << (pdeg(a) - d))
    end
    return a
end
pmulmod(a, b, f) = pmod(pmul(a, b), f)
function ppowmod(a::BigInt, e::Integer, f::BigInt)
    r, a = big(1), pmod(a, f)
    e = big(e)
    while e > 0
        isodd(e) && (r = pmulmod(r, a, f))
        a = pmulmod(a, a, f)
        e >>= 1
    end
    return r
end
function pgcd(a::BigInt, b::BigInt)
    while !iszero(b)
        a, b = b, pmod(a, b)
    end
    return a
end
# x^(2^k) mod f by k squarings
function xpow2k(k, f)
    r = pmod(big(2), f)
    for _ in 1:k
        r = pmulmod(r, r, f)
    end
    return r
end
# Composition g(h) mod f, g as a bit pattern: Horner.
function pcompose(g::BigInt, h::BigInt, f::BigInt)
    r = big(0)
    for i in pdeg(g):-1:0
        r = xor(pmulmod(r, h, f), (g >> i) & 1)
    end
    return r
end

prime_divisors_small(n) = [p for p in 2:n if n % p == 0 && all(p % q != 0 for q in 2:(p - 1))]

# Rabin: f of degree n is irreducible iff x^(2^n) ≡ x and gcd(x^(2^(n/p)) - x, f) = 1 for every
# prime p | n.
function is_irreducible(f::BigInt)
    n = pdeg(f)
    n >= 1 || return false
    xpow2k(n, f) == pmod(big(2), f) || return false
    return all(p -> pdeg(pgcd(f, xor(xpow2k(n ÷ p, f), pmod(big(2), f)))) == 0,
               prime_divisors_small(n))
end

# --- Factorisation of 2^n - 1 (n ≤ 64) ---------------------------------------------------------

function is_probable_prime(n::BigInt)
    n < 2 && return false
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
        n == p && return true
        n % p == 0 && return false
    end
    d, s = n - 1, 0
    while iseven(d)
        d >>= 1
        s += 1
    end
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)  # deterministic below 3.3e24
        x = powermod(big(a), d, n)
        (x == 1 || x == n - 1) && continue
        composite = true
        for _ in 1:(s - 1)
            x = powermod(x, 2, n)
            if x == n - 1
                composite = false
                break
            end
        end
        composite && return false
    end
    return true
end
function rho(n::BigInt)
    for c in 1:100
        x, y, d = big(2), big(2), big(1)
        while d == 1
            x = mod(x * x + c, n)
            y = mod(y * y + c, n)
            y = mod(y * y + c, n)
            d = gcd(abs(x - y), n)
        end
        d != n && return d
    end
    error("rho failed on $n")
end
function prime_factors(n::BigInt)
    fs = Set{BigInt}()
    for p in 2:10_000
        while n % p == 0
            push!(fs, big(p))
            n ÷= p
        end
    end
    stack = n > 1 ? [n] : BigInt[]
    while !isempty(stack)
        m = pop!(stack)
        if is_probable_prime(m)
            push!(fs, m)
        else
            d = rho(m)
            push!(stack, d, m ÷ d)
        end
    end
    return sort!(collect(fs))
end

# f primitive: x has order 2^n - 1 modulo f (f irreducible).
function is_primitive(f::BigInt)
    n = pdeg(f)
    q = big(2)^n - 1
    isodd(f) || return false                       # the root 0 (f = x) is not a unit
    n == 1 && return true
    return all(p -> ppowmod(big(2), q ÷ p, f) != 1, prime_factors(q))
end

# C_m(x^((2^n-1)/(2^m-1))) ≡ 0 modulo C_n.
compatible(fm::BigInt, fn::BigInt) =
    iszero(pcompose(fm, ppowmod(big(2), (big(2)^pdeg(fn) - 1) ÷ (big(2)^pdeg(fm) - 1), fn), fn))

full_poly(n, low) = (big(1) << n) | big(low)
const TABLE = Dict(n => full_poly(n, low) for (n, low) in CONWAY_TABLE)

# --- The table --------------------------------------------------------------------------------

@testset "Conway table (Lübeck's data)" begin
    @test conway_degrees() == sort!(collect(keys(TABLE)))
    @test all(n -> haskey(TABLE, n), 1:92)
    @test !haskey(TABLE, 128)
    # the entries named in the literature (Lübeck's list): C_8 = x^8 + x^4 + x^3 + x^2 + 1
    @test TABLE[8] == big(0x11d)
    @test TABLE[4] == big(0b10011)
    for n in sort!(collect(keys(TABLE)))
        f = TABLE[n]
        @test is_irreducible(f)
        for m in 1:(n - 1)
            n % m == 0 && haskey(TABLE, m) && @test compatible(TABLE[m], f)
        end
        n <= 64 && @test is_primitive(f)
    end
end

# Conway's ordering for p = 2: compare the coefficients from x^(n-1) down to x^0 (the signs in
# Lübeck's definition do not matter in characteristic 2), i.e. the low bits g of f = x^n + g as
# integers. The Conway polynomial is the least monic primitive polynomial compatible with C_m
# for every m | n.
@testset "the table entries are the least such polynomials (n ≤ 16)" begin
    for n in 1:16
        cands = 0:((1 << n) - 1)
        least = findfirst(cands) do g
            f = full_poly(n, g)
            is_irreducible(f) && is_primitive(f) &&
                all(m -> n % m != 0 || compatible(TABLE[m], f), 1:(n - 1))
        end
        @test full_poly(n, cands[least]) == TABLE[n]
    end
end

# --- Field arithmetic -------------------------------------------------------------------------

# Reference product and inverse, from the BigInt oracle.
modulus_poly(F) = full_poly(degree(F), FiniteFieldArithmetic.field_modulus(F))
ref_mul(x::F, y::F) where {F} = pmulmod(big(bits(x)), big(bits(y)), modulus_poly(F))
ref_inv(x::F) where {F} = ppowmod(big(bits(x)), big(2)^degree(F) - 2, modulus_poly(F))

const SMALL = filter(n -> n <= 10, conway_degrees())

function field_samples(F, rng)
    degree(F) <= 8 && return collect(elements(F))
    xs = [rand(rng, F) for _ in 1:300]
    append!(xs, (zero(F), one(F), F(max_value(F)), F(2 % storagetype(F))))
    return xs
end
max_value(F) = (big(1) << degree(F)) - 1

@testset "Conway fields: products and inverses against the oracle" begin
    rng = Xoshiro(11)
    for n in conway_degrees()
        F = conway_field(n)
        @testset "n = $n" begin
            @test degree(F) == n
            @test storagetype(F) == (n <= 8 ? UInt8 : n <= 16 ? UInt16 : n <= 32 ? UInt32 :
                                     n <= 64 ? UInt64 : UInt128)
            @test is_conway(F)
            @test conway_field(Val(n)) === F
            xs = field_samples(F, rng)
            for x in xs
                y = xs[rand(rng, eachindex(xs))]
                @test big(bits(x * y)) == ref_mul(x, y)
                @test x * y == y * x
                @test (x + y) * x == x * x + y * x
                if !iszero(x)
                    @test isone(x * inv(x))
                    degree(F) <= 64 && @test big(bits(inv(x))) == ref_inv(x)
                end
            end
            @test_throws DivideError inv(zero(F))
            α = conway_generator(F)
            @test big(bits(α)) == pmod(big(2), modulus_poly(F))
            # α is a root of C_n
            @test iszero(sum((α^i for i in 0:n if isodd(modulus_poly(F) >> i)); init = zero(F)))
            # α is primitive (orders checked for n ≤ 64 in the table test): α^(2^n - 1) = 1
            @test isone(α^(big(2)^n - 1))
        end
    end
end

@testset "exhaustive products and inverses (n ≤ 10)" begin
    for n in SMALL
        F = conway_field(n)
        xs = collect(elements(F))
        for x in xs, y in xs
            @test big(bits(x * y)) == ref_mul(x, y)
        end
        for x in xs[2:end]
            @test big(bits(inv(x))) == ref_inv(x)
        end
    end
end

@testset "construction and checks" begin
    F = conway_field(8)
    @test F(0x1b) isa F
    @test bits(F(0x1b)) === 0x1b
    @test_throws ArgumentError conway_field(7)(0x80)      # 2^7 is not below 2^7
    @test_throws ArgumentError conway_field(128)          # not in the database
    @test_throws ArgumentError conway_field(0)
    @test_throws ArgumentError poly_field(8, 0x00)        # x^8 is reducible
    @test_throws ArgumentError poly_field(8, 0x1f)        # six terms: x + 1 divides it
    @test poly_field(8, 0x1d) === F                       # the Conway modulus gives the Conway type
    @test poly_field(8, 0x1b) === GF256_AES
    @test !is_conway(GF256_AES)
    @test !is_conway(GF256)
    @test FiniteFieldArithmetic.field_modulus(F) === 0x1d
    # a polynomial-basis element is not equal to a nimber or an element of another basis
    @test F(3) != GF256(3)
    @test F(3) != GF256_AES(3)
    @test F(3) == F(3)
    @test hash(F(3)) == hash(F(3))
end

# --- AES and GHASH ------------------------------------------------------------------------------

@testset "AES field GF(2)[x]/(x^8 + x^4 + x^3 + x + 1)" begin
    A = GF256_AES
    @test degree(A) == 8
    # FIPS-197 (2001), Sec. 4.2: {57} • {83} = {c1}; Sec. 4.2.1: {57} • {13} = {fe}
    @test A(0x57) * A(0x83) == A(0xc1)
    @test A(0x57) * A(0x13) == A(0xfe)
    # FIPS-197, Sec. 5.1.1: the S-box input {53} has inverse {ca}
    @test inv(A(0x53)) == A(0xca)
    for x in elements(A), y in (A(0x57), A(0x83), A(0xff))
        @test big(bits(x * y)) == ref_mul(x, y)
    end
end

@testset "GHASH field GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)" begin
    G = GF2_128_GHASH
    @test degree(G) == 128
    @test storagetype(G) === UInt128
    @test is_irreducible(modulus_poly(G))
    rng = Xoshiro(12)
    for _ in 1:300
        x, y = rand(rng, G), rand(rng, G)
        @test big(bits(x * y)) == ref_mul(x, y)
        iszero(x) || @test isone(x * inv(x))
    end
    # the reduction: x^127 · x = x^128 = x^7 + x^2 + x + 1
    @test G(UInt128(1) << 127) * G(2) == G(0x87)
end

# --- Embeddings between Conway fields -----------------------------------------------------------

@testset "Conway embeddings F_{2^m} → F_{2^n}, m | n" begin
    rng = Xoshiro(13)
    pairs = [(m, n) for n in conway_degrees() for m in conway_degrees() if m < n && n % m == 0 &&
             n <= 72]
    for (m, n) in pairs
        Fm, Fn = conway_field(m), conway_field(n)
        e = (big(2)^n - 1) ÷ (big(2)^m - 1)
        @test embed(Fn, conway_generator(Fm)) == conway_generator(Fn)^e
        xs = field_samples(Fm, rng)
        for _ in 1:30
            x, y = rand(rng, xs), rand(rng, xs)
            @test embed(Fn, x * y) == embed(Fn, x) * embed(Fn, y)
            @test embed(Fn, x + y) == embed(Fn, x) + embed(Fn, y)
        end
        @test embed(Fn, one(Fm)) == one(Fn)
        @test embed(Fn, zero(Fm)) == zero(Fn)
    end
    # transitivity: F_4 → F_8 → F_24 equals F_4 → F_24
    for x in elements(conway_field(4))
        @test embed(conway_field(24), embed(conway_field(8), x)) == embed(conway_field(24), x)
    end
    @test embed(conway_field(8), conway_field(8)(0x1b)) === conway_field(8)(0x1b)
    @test_throws ArgumentError embed(conway_field(8), conway_field(3)(1))     # 3 ∤ 8
    # `embed` goes through On_2 (three byte-table maps); the reference is the definition,
    # α_m ↦ α_n^((2^n-1)/(2^m-1)) by Horner, for every table pair m | n (also above 72)
    for n in conway_degrees(), m in conway_degrees()
        (m < n && n % m == 0) || continue
        Fm, Fn = conway_field(m), conway_field(n)
        @test embed(Fn, conway_generator(Fm)) == FiniteFieldArithmetic.embed_horner(Fn, conway_generator(Fm))
        for _ in 1:(n <= 72 ? 8 : 3)
            x = rand(rng, Fm)
            @test embed(Fn, x) == FiniteFieldArithmetic.embed_horner(Fn, x)
        end
    end
    @test (@inferred embed(conway_field(Val(126)), conway_field(Val(21))(5))) isa conway_field(126)
    @test (@inferred embed(conway_field(Val(64)), conway_field(Val(8))(5))) isa conway_field(64)
end

# --- Nimbers and Conway fields ------------------------------------------------------------------

const NIMBERS = (GF2, GF4, GF16, GF256, GF2_16, GF2_32, GF2_64)

@testset "isomorphisms between nimber and Conway fields of degree 2^k" begin
    rng = Xoshiro(14)
    for (k, N) in enumerate(NIMBERS)
        n = degree(N)
        C = conway_field(n)
        α = conway_generator(C)
        r = embed(N, α)
        # r is a root of C_n in the nimber field
        @test iszero(sum((r^i for i in 0:n if isodd(modulus_poly(C) >> i)); init = zero(N)))
        if k > 1
            # compatible with the level below: r^(2^(n/2) + 1) is the image of α_{n/2}
            Nprev = NIMBERS[k - 1]
            rprev = embed(Nprev, conway_generator(conway_field(n ÷ 2)))
            @test r^((big(2)^(n ÷ 2)) + 1) == N(rprev)
            # the convention: of the two compatible roots r and r^(2^(n/2)), the smaller integer
            @test bits(r) < bits(r^(big(2)^(n ÷ 2)))
        end
        xs = field_samples(C, rng)
        for _ in 1:200
            x, y = rand(rng, xs), rand(rng, xs)
            @test embed(N, x * y) == embed(N, x) * embed(N, y)
            @test embed(N, x + y) == embed(N, x) + embed(N, y)
            @test embed(C, embed(N, x)) == x                      # inverse maps
            u = rand(rng, N)
            @test embed(N, embed(C, u)) == u
        end
        if n <= 16                                                 # bijective
            @test length(Set(embed(N, x) for x in elements(C))) == 2^n
        end
    end
    # the squares commute: Conway embedding then isomorphism = isomorphism then nimber inclusion
    for (k, N) in enumerate(NIMBERS), (j, M) in enumerate(NIMBERS)
        j < k || continue
        Cm, Cn = conway_field(degree(M)), conway_field(degree(N))
        for _ in 1:50
            x = rand(rng, Cm)
            @test embed(N, embed(Cn, x)) == N(embed(M, x))
            @test embed(N, x) == N(embed(M, x))                  # direct, through the subfield
            @test embed(Cn, embed(M, x)) == embed(Cn, x)
        end
    end
end

@testset "printing and type stability" begin
    F = conway_field(8)
    @test string(F(0x1b)) == "0x1b"
    @test repr(conway_field(4)(0xb)) == "0xb ∈ GF(2^4)"
    for n in (3, 8, 16, 33, 64, 127)
        F = conway_field(n)
        x, y = F(5), F(3)
        @test (@inferred x * y) isa F
        @test (@inferred inv(x)) isa F
        @test (@inferred x / y) isa F
    end
    @test (@inferred conway_field(Val(8))) === conway_field(8)
end
