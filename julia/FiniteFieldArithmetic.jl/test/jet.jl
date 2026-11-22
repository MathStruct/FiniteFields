# JET.jl: no possible errors found by abstract interpretation in the package, and no runtime
# dispatch in the arithmetic hot paths. (DispatchDoctor's `@stable` in the source additionally
# throws on any type-unstable call to an arithmetic method; the test suite exercises them all.)
using FiniteFieldArithmetic
using FiniteFieldArithmetic: mul, inverse, Recursive, MulTable, LogTable, LogTable16, CLMul,
    ScalarMatMul, TableMatMul, CLMulMatMul, BitslicedMatMul, BySizeMatMul, matmul!,
    default_matmul_strategy, mul_elementwise!, ScalarConstMul,
    LazyMulBy, const_mul_broadcasted
using JET, Test

@testset "JET" begin
    JET.test_package(FiniteFieldArithmetic; target_modules = (FiniteFieldArithmetic,))
    a, b = GF256(0x53), GF256(0xca)
    for s in (Recursive(), MulTable(), LogTable(), LogTable16(), CLMul())
        @test_opt mul(s, a, b)
        @test_opt inverse(s, a)
    end
    @test_opt a + b
    @test_opt a * b
    @test_opt a / b
    @test_opt a^7
    @test_opt GF16(3) * GF256(5)
    for F in (GF2_16, GF2_32, GF2_64, GF2_128)
        x, y = F(0x53), F(0xca)
        for s in (Recursive(), MulTable(), LogTable(), LogTable16(), CLMul())
            @test_opt mul(s, x, y)
            @test_opt inverse(s, x)
        end
        @test_opt x^7
        @test_opt minimal_level(x)                     # J9 (reduce_field is unstable by design)
        @test_opt minimal_degree(x)
        @test_opt inv(x)
        @test_opt x / y
    end
    # polynomial-basis fields (J1a)
    for F in (conway_field(Val(3)), conway_field(Val(8)), conway_field(Val(64)),
              conway_field(Val(127)), GF256_AES, GF2_128_GHASH)
        x, y = F(5), F(3)
        @test_opt x * y
        @test_opt inv(x)
        @test_opt x / y
        @test_opt x^7
    end
    @test_opt conway_field(Val(8))
    # table strategies for small polynomial-basis fields (J1a)
    for F in (conway_field(Val(4)), conway_field(Val(8)), GF256_AES, conway_field(Val(13)),
              conway_field(Val(16)))
        x, y = F(5), F(3)
        @test_opt mul(LogTable(), x, y)
        @test_opt inverse(LogTable(), x)
        if degree(F) <= 8
            @test_opt mul(MulTable(), x, y)
            @test_opt inverse(MulTable(), x)
        end
    end
    # rank-encoded fields (J10)
    for F in (nim_field(Val(3)), nim_field(Val(12)), nim_field(Val(107)), nim_field(Val(127)))
        x, y = F(5), F(3)
        @test_opt x * y
        @test_opt inv(x)
        @test_opt x / y
        @test_opt minimal_degree(x)
    end
    @test_opt embed(nim_field(Val(12)), nim_field(Val(3))(5))
    # Conway fields ↔ rank-encoded fields (J10)
    @test_opt embed(nim_field(Val(12)), conway_field(Val(3))(5))
    @test_opt embed(nim_field(Val(24)), conway_field(Val(8))(5))
    @test_opt embed(nim_field(Val(126)), conway_field(Val(21))(5))
    @test_opt embed(conway_field(Val(12)), nim_field(Val(3))(5))
    @test_opt embed(conway_field(Val(24)), GF256(5))
    # pseudo-Conway fields (J1a)
    for n in (93, 122, 128)
        P = pseudo_conway_field(Val(n))
        @test_opt P(5) * P(3)
        @test_opt inv(P(5))
        @test_opt embed(nim_field(Val(n)), P(5))
        @test_opt embed(P, nim_field(Val(n))(5))
    end
    @test_opt embed(pseudo_conway_field(Val(124)), conway_field(Val(62))(5))
    # inversion strategies (J3)
    for F in (GF256, GF2_16, GF2_64, GF2_128, conway_field(Val(8)), conway_field(Val(64)),
              conway_field(Val(127)), GF2_128_GHASH)
        x = F(5)
        for s in (FiniteFieldArithmetic.Fermat(), FiniteFieldArithmetic.ItohTsujii(),
                  FiniteFieldArithmetic.Euclid())
            @test_opt inverse(s, x)
        end
        @test_opt inv(x)
    end
    # bulk operations (J8)
    for F in (GF256, GF2_16, GF2_32, GF2_64, GF2_128)
        x = F(0x53)
        A, B, C = fill(x, 3, 3), fill(x, 3, 3), fill(x, 3, 3)
        m = MulBy(x)
        @test_opt m(x)
        for s in (ScalarMatMul(MulTable()), TableMatMul(), CLMulMatMul(), BitslicedMatMul(),
                  default_matmul_strategy(F), BySizeMatMul(TableMatMul(), BitslicedMatMul(), 2))
            @test_opt matmul!(s, C, A, B)
        end
        @test_opt A * B
        v, w = fill(x, 3), fill(x, 3)
        @test_opt matmul!(CLMulMatMul(), w, A, v)                # matrix × vector (FF-P2)
        @test_opt A * v
        # constant times array (J8c)
        a = fill(x, 70)
        for s in (ScalarConstMul(), LazyMulBy(0), LazyMulBy(typemax(Int)))
            @test_opt const_mul_broadcasted(s, x, a)
            @test_opt Base.Broadcast.materialize(const_mul_broadcasted(s, x, a))
        end
        @test_opt m(GF2(1))                                       # fallback for other operands
        @test_opt Base.Broadcast.materialize!(similar(a),
            Base.Broadcast.broadcasted(+, const_mul_broadcasted(LazyMulBy(50), x, a), a))
        @test_opt x * a                                # Base broadcasts: the same hook as x .* a
    end
    for F in (GF256, GF2_16, GF2_32, GF2_64, GF2_128)
        v = BitslicedVector(fill(F(3), 70))
        @test_opt mul_elementwise!(v, v, v)
    end
end
