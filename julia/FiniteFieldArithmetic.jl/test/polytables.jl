# J1a: table strategies for small polynomial-basis fields: `MulTable()` (a full product table and
# an inverse table, degree ≤ 8) and `LogTable()` (logarithm and exponential tables to the base of
# the least primitive element, degree ≤ 16; for Conway fields that base is α_n = x).
#
# Oracle: the carry-less product `mul(CLMul(), a, b)` (tested against BigInt polynomials in
# test/conway.jl) and the inverses of `Euclid()` (test/inversion.jl).

using FiniteFieldArithmetic
using FiniteFieldArithmetic: bits, mul, inverse, MulTable, LogTable, CLMul, Euclid,
    default_strategy, default_inv_strategy, log_generator, field_modulus, MulStrategy, InvStrategy
using Random, Test

# Every Conway field of degree ≤ 16, the AES field, a non-Conway field with x not primitive
# (x^4 + x^3 + x^2 + x + 1: x has order 5), and the internal polynomial bases of nim_field.
const TABLE_FIELDS = Any[conway_field(n) for n in 1:16]
append!(TABLE_FIELDS, [GF256_AES, poly_field(4, 0b1111)])
append!(TABLE_FIELDS, [typeof(FiniteFieldArithmetic.to_nimpoly(nim_field(n)(1))) for n in (3, 6, 12)])

const MT_FIELDS = filter(F -> degree(F) <= 8, TABLE_FIELDS)

samples(F, rng) = degree(F) <= 8 ? collect(elements(F)) : vcat(rand(rng, F, 3000), [zero(F), one(F)])

function order(x::F) where {F}
    k, y = 1, x
    while !isone(y)
        y *= x
        k += 1
    end
    return k
end

@testset "the base of the logarithms" begin
    for F in TABLE_FIELDS
        g = log_generator(F)
        @test g isa F
        q = (1 << degree(F)) - 1
        @test order(g) == q                                  # primitive
        @test all(order(F(b)) < q for b in 1:(Int(bits(g)) - 1))   # and the least such
        if is_conway(F)
            @test g == conway_generator(F)                   # α_n = x
        end
    end
    @test log_generator(GF256_AES) == GF256_AES(0x03)        # x is not primitive for AES
    @test bits(log_generator(poly_field(4, 0b1111))) == 0x03
end

@testset "MulTable on fields of degree ≤ 8" begin
    for F in MT_FIELDS
        @testset "$F" begin
            xs = collect(elements(F))
            @test all(mul(MulTable(), a, b) == mul(CLMul(), a, b) for a in xs, b in xs)
            @test all(inverse(MulTable(), a) == inverse(Euclid(), a) for a in xs if !iszero(a))
            @test_throws DivideError inverse(MulTable(), zero(F))
        end
    end
    F = conway_field(9)
    @test_throws ArgumentError mul(MulTable(), F(3), F(5))
    @test_throws ArgumentError inverse(MulTable(), F(3))
end

@testset "LogTable on fields of degree ≤ 16" begin
    rng = Xoshiro(41)
    for F in TABLE_FIELDS
        @testset "$F" begin
            xs = samples(F, rng)
            ys = shuffle(rng, xs)
            @test all(mul(LogTable(), a, b) == mul(CLMul(), a, b) for (a, b) in zip(xs, ys))
            @test all(mul(LogTable(), a, zero(F)) == zero(F) == mul(LogTable(), zero(F), a)
                      for a in xs)
            if degree(F) <= 8
                @test all(mul(LogTable(), a, b) == mul(CLMul(), a, b) for a in xs, b in xs)
            end
            @test all(inverse(LogTable(), a) == inverse(Euclid(), a) for a in xs if !iszero(a))
            @test_throws DivideError inverse(LogTable(), zero(F))
        end
    end
    # all of GF(2^16), Conway: products with a fixed factor, and every inverse
    C = conway_field(16)
    c = C(0xbeef)
    @test all(mul(LogTable(), a, c) == mul(CLMul(), a, c) for a in elements(C))
    @test all(inverse(LogTable(), a) == inverse(Euclid(), a) for a in elements(C) if !iszero(a))
    F = conway_field(17)
    @test_throws ArgumentError mul(LogTable(), F(3), F(5))
    @test_throws ArgumentError inverse(LogTable(), F(3))
end

@testset "defaults of * and inv" begin
    rng = Xoshiro(42)
    for F in vcat(TABLE_FIELDS, Any[conway_field(n) for n in (17, 32, 64, 127)], [GF2_128_GHASH])
        s, t = default_strategy(F), default_inv_strategy(F)
        @test s isa MulStrategy
        @test t isa Union{MulStrategy, InvStrategy}
        a, b = rand(rng, F), rand(rng, F)
        iszero(b) && (b = one(F))
        @test a * b == mul(s, a, b) == mul(CLMul(), a, b)
        @test inv(b) == inverse(t, b) == inverse(Euclid(), b)
        degree(F) > 16 && @test s === CLMul()                # tables only for small degrees
    end
end

@testset "type stability" begin
    for F in (conway_field(Val(4)), conway_field(Val(8)), GF256_AES, conway_field(Val(13)),
              conway_field(Val(16)))
        a, b = F(5), F(3)
        @test (@inferred mul(LogTable(), a, b)) isa F
        @test (@inferred inverse(LogTable(), a)) isa F
        if degree(F) <= 8
            @test (@inferred mul(MulTable(), a, b)) isa F
            @test (@inferred inverse(MulTable(), a)) isa F
        end
        @test (@inferred a * b) isa F
        @test (@inferred inv(a)) isa F
    end
end
