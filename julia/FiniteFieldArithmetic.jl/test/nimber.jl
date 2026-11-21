# Nimber fields GF(2^(2^K)), K = 0..3: GF(2), GF(4), GF(16), GF(256), all stored in UInt8.
#
# Oracles, independent of the implementation:
# - the definition of nim-multiplication (Conway, On Numbers and Games, ch. 6):
#     a ⊗ b = mex { (a' ⊗ b) ⊕ (a ⊗ b') ⊕ (a' ⊗ b') : a' < a, b' < b },
#   evaluated by brute force below 16;
# - the Fermat-power rules: for F = 2^(2^k) and x < F, F ⊗ x = F·x (ordinary product) and
#   F ⊗ F = 3F/2;
# - the field axioms, checked exhaustively on GF(256) (so the multiplication really is a field).

using FiniteFieldArithmetic
using FiniteFieldArithmetic: bits, mul, inverse, Recursive, MulTable, LogTable
using Test

const STRATEGIES = (Recursive(), MulTable(), LogTable())

# Brute-force nim-multiplication from the definition (mex), for a, b < n.
function mex_table(n)
    T = zeros(Int, n, n)
    for a in 0:(n - 1), b in 0:(n - 1)
        seen = falses(n * n + 1)
        for a′ in 0:(a - 1), b′ in 0:(b - 1)
            v = T[a′ + 1, b + 1] ⊻ T[a + 1, b′ + 1] ⊻ T[a′ + 1, b′ + 1]
            seen[v + 1] = true
        end
        T[a + 1, b + 1] = findfirst(!, seen) - 1
    end
    return T
end

@testset "types and constants" begin
    @test GF2 === Nimber{0, UInt8}
    @test GF4 === Nimber{1, UInt8}
    @test GF16 === Nimber{2, UInt8}
    @test GF256 === Nimber{3, UInt8}
    @test isbitstype(GF256)
    @test sizeof(GF256) == 1                       # no wider integer than needed
    for (F, n) in ((GF2, 1), (GF4, 2), (GF16, 4), (GF256, 8))
        @test characteristic(F) == 2
        @test degree(F) == n
        @test length(collect(elements(F))) == 2^n
        @test allunique(elements(F))
    end
end

@testset "construction" begin
    @test bits(GF256(0x1b)) === 0x1b
    @test bits(GF256(27)) === 0x1b                 # an integer is the nimber with that value
    @test bits(GF16(15)) === 0x0f
    @test_throws ArgumentError GF256(256)
    @test_throws ArgumentError GF256(-1)
    @test_throws ArgumentError GF16(16)
    @test_throws ArgumentError GF2(2)
    @test_throws ArgumentError Nimber{4, UInt8}(1)  # GF(2^16) does not fit a UInt8
    @test zero(GF256) == GF256(0) && iszero(zero(GF256))
    @test one(GF256) == GF256(1) && isone(one(GF256))
end

@testset "addition is XOR, characteristic 2" begin
    for a in elements(GF256), b in elements(GF256)
        @test bits(a + b) == bits(a) ⊻ bits(b)
        @test a - b == a + b
    end
    for a in elements(GF256)
        @test a + a == zero(GF256)
        @test -a == a
    end
end

@testset "multiplication agrees with the mex definition below 16" begin
    T = mex_table(16)
    @test T[3, 3] == 3 && T[5, 5] == 6 && T[9, 9] == 13   # 2⊗2, 4⊗4, 8⊗8
    for s in STRATEGIES, a in 0:15, b in 0:15
        @test bits(mul(s, GF16(a), GF16(b))) == T[a + 1, b + 1]
        @test bits(mul(s, GF256(a), GF256(b))) == T[a + 1, b + 1]
    end
end

@testset "Fermat-power rules" begin
    for F in (2, 4, 16), x in 0:(F - 1)
        @test bits(GF256(F) * GF256(x)) == F * x
    end
    @test GF256(2) * GF256(2) == GF256(3)
    @test GF256(4) * GF256(4) == GF256(6)
    @test GF256(16) * GF256(16) == GF256(24)
end

@testset "strategies agree exhaustively on GF(256)" begin
    for a in elements(GF256), b in elements(GF256)
        r = mul(Recursive(), a, b)
        @test mul(MulTable(), a, b) == r
        @test mul(LogTable(), a, b) == r
    end
    for a in elements(GF256)
        iszero(a) && continue
        r = inverse(Recursive(), a)
        @test inverse(MulTable(), a) == r
        @test inverse(LogTable(), a) == r
    end
end

@testset "field axioms on GF(256), exhaustive" begin
    E = collect(elements(GF256))
    @test all(a * b == b * a for a in E, b in E)
    @test all(a * one(GF256) == a && a * zero(GF256) == zero(GF256) for a in E)
    @test all((a * b) * c == a * (b * c) for a in E, b in E, c in E)
    @test all(a * (b + c) == a * b + a * c for a in E, b in E, c in E)
    @test all(a * inv(a) == one(GF256) for a in E if !iszero(a))
    @test_throws DivideError inv(zero(GF256))
    @test all(a / b * b == a for a in E, b in E if !iszero(b))
end

@testset "powers, Frobenius, cyclic group" begin
    E = collect(elements(GF256))
    @test all(a^256 == a for a in E)                       # Frobenius fixes GF(256)
    @test all(a^255 == one(GF256) for a in E if !iszero(a))
    @test all((a + b)^2 == a^2 + b^2 for a in E, b in E)   # squaring is additive
    @test all(a^-1 == inv(a) && a^-3 == inv(a^3) for a in E if !iszero(a))
    @test zero(GF256)^0 == one(GF256) && zero(GF256)^5 == zero(GF256)
    @test_throws DivideError zero(GF256)^-1
    order(a) = findfirst(k -> isone(a^k), 1:255)
    @test any(order(a) == 255 for a in E if !iszero(a))    # a generator exists
    @test all(255 % order(a) == 0 for a in E if !iszero(a))
end

@testset "subfields are nested as integers" begin
    # GF(2) ⊂ GF(4) ⊂ GF(16) ⊂ GF(256) with the same bit patterns: the embedding is the identity
    # on bits, and products in a subfield agree with products in GF(256).
    for (F, n) in ((GF2, 2), (GF4, 4), (GF16, 16)), a in 0:(n - 1), b in 0:(n - 1)
        @test bits(F(a) * F(b)) == bits(GF256(a) * GF256(b))
        @test GF256(F(a)) == GF256(a)
    end
    @test GF16(3) * GF256(16) == GF256(3) * GF256(16)      # promotion embeds
    @test promote_type(GF16, GF256) === GF256
    @test GF16(GF256(15)) == GF16(15)                      # restriction when it fits
    @test_throws ArgumentError GF16(GF256(16))
    @test GF16(7) == GF256(7)
    @test hash(GF16(7)) == hash(GF256(7))
end

@testset "equality with other numbers is false, never an error" begin
    @test GF256(7) != 7
    @test 7 != GF256(7)
    @test GF256(1) != 1.0
    @test GF256(7) in Any[7, GF256(7)]
    @test length(Set(Any[GF256(1), 1, GF16(1)])) == 2   # GF16(1) == GF256(1)
end

@testset "random elements" begin
    @test rand(GF256) isa GF256
    v = rand(GF16, 1000)
    @test eltype(v) === GF16
    @test all(bits(x) < 16 for x in v)
end

@testset "type stability" begin
    a, b = GF256(0x53), GF256(0xca)
    for s in STRATEGIES
        @test (@inferred mul(s, a, b)) isa GF256
        @test (@inferred inverse(s, a)) isa GF256
    end
    @test (@inferred a * b) isa GF256
    @test (@inferred a + b) isa GF256
    @test (@inferred a / b) isa GF256
    @test (@inferred a^7) isa GF256
    @test (@inferred GF16(3) * GF256(5)) isa GF256
end

@testset "elements of large fields (#4)" begin
    for F in (GF2_64, GF2_128)
        E = elements(F)
        @test Base.IteratorSize(E) == Base.SizeUnknown()
        @test eltype(E) == F
        @test_throws OverflowError length(E)
        @test collect(Iterators.take(E, 5)) == [F(i) for i in 0:4]
        @test first(E, 3) == [F(0), F(1), F(2)]
    end
    for F in (GF2, GF256, GF2_16, GF2_32)
        @test Base.IteratorSize(elements(F)) == Base.HasLength()
        @test length(elements(F)) == 2^degree(F)
    end
    @test last(collect(elements(GF16))) == GF16(15)
end
