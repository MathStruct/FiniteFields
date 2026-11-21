# Bulk and array operations (backlog J8): random sampling of arrays, broadcasting, multiplication
# by a fixed constant (`MulBy`), matrix products over the nimber fields (`matmul!`, `*`, `mul!`),
# and bitsliced vectors (`BitslicedVector`).
#
# Oracles, independent of the bulk code:
# - every product is compared with `mul(Recursive(), …)`, the table-free reference;
# - matrix products with the textbook triple sum of `Recursive` products;
# - bitsliced vectors with the element-wise products of the plain vectors;
# - structural checks: associativity of the matrix product, the identity matrix, linearity of
#   multiplication by a constant.

using FiniteFieldArithmetic
using FiniteFieldArithmetic: bits, mul, Recursive, MulTable, LogTable16, CLMul, has_pclmul,
    MatMulStrategy, ScalarMatMul, TableMatMul, CLMulMatMul, BitslicedMatMul, BySizeMatMul,
    choose_matmul, bitsliced_threshold, matmul!, default_matmul_strategy, mul_elementwise!,
    clmul_by_columns, clmul_columns_add!, clmul_transposed_add!
using LinearAlgebra, Random, Test

rng = Xoshiro(20261121)
const LEVELS = (GF2, GF4, GF16, GF256, GF2_16, GF2_32, GF2_64, GF2_128)
const MATMUL_STRATEGIES = (ScalarMatMul(Recursive()), ScalarMatMul(MulTable()),
                           ScalarMatMul(LogTable16()), TableMatMul(), CLMulMatMul(),
                           BitslicedMatMul(), BySizeMatMul(ScalarMatMul(Recursive()),
                                                           BitslicedMatMul(), 5))

refmul(a, b) = mul(Recursive(), a, b)
function refmatmul(A::AbstractMatrix{F}, B::AbstractVecOrMat{F}) where {F}
    C = zeros(F, size(A, 1), size(B, 2))
    for i in axes(A, 1), j in axes(B, 2), k in axes(A, 2)
        C[i, j] += refmul(A[i, k], B[k, j])
    end
    return B isa AbstractVector ? vec(C) : C
end
# Random elements with the extreme values mixed in.
function samples(F, n)
    x = rand(rng, F, n)
    n >= 3 && (x[1] = zero(F); x[2] = one(F); x[3] = F(FiniteFieldArithmetic.max_bits(F)))
    return x
end

@testset "random arrays, $F" for F in LEVELS
    T = FiniteFieldArithmetic.storagetype(F)
    x = rand(Xoshiro(7), F, 1000)
    @test x isa Vector{F} && length(x) == 1000
    @test x == rand(Xoshiro(7), F, 1000)                     # reproducible
    @test all(v -> bits(v) <= FiniteFieldArithmetic.max_bits(F), x)
    M = rand(rng, F, 3, 4)
    @test M isa Matrix{F} && size(M) == (3, 4)
    v = zeros(F, 20)
    rand!(rng, view(v, 2:2:20))                               # non-contiguous: generic path
    @test all(iszero, v[1:2:20])
    if degree(F) <= 8                                         # every element shows up
        @test length(unique(rand(rng, F, 4000))) == 2^degree(F)
    end
    if degree(F) >= 8                                         # every bit varies
        y = bits.(rand(rng, F, 200))
        @test reduce(|, y) == FiniteFieldArithmetic.max_bits(F)
        @test reduce(&, y) == zero(T)
    end
end

@testset "broadcasting, $F" for F in LEVELS
    a, b = samples(F, 100), samples(F, 100)
    c = rand(rng, F)
    @test a .* b == refmul.(a, b)
    @test c .* a == refmul.(Ref(c), a)
    @test a .+ b == [x + y for (x, y) in zip(a, b)]
    @test a .^ 3 == [refmul(x, refmul(x, x)) for x in a]
    nz = filter(!iszero, a)
    @test all(isone, nz .* inv.(nz))
    @test sum(a) == foldl(+, a; init = zero(F))
    out = similar(a)
    f!(out, a, b, c) = (out .= a .* b .+ c; out)
    f!(out, a, b, c)
    @test (@allocated f!(out, a, b, c)) == 0                  # fused, no temporaries
    @test out == refmul.(a, b) .+ c
    @test isbitstype(F)                                       # usable in GPU arrays (not tested)
end

@testset "multiplication by a constant (MulBy), $F" for F in LEVELS
    for c in (zero(F), one(F), samples(F, 6)...)
        m = MulBy(c)
        x = samples(F, 300)
        @test m.(x) == refmul.(Ref(c), x)
        x1, x2 = rand(rng, F), rand(rng, F)
        @test m(x1 + x2) == m(x1) + m(x2)                     # F_2-linear
    end
end

@testset "matrix products, $F" for F in LEVELS
    @test default_matmul_strategy(F) isa MatMulStrategy
    shapes = ((1, 1, 1), (7, 5, 3), (4, 9, 6), (16, 16, 16), (0, 3, 2), (3, 0, 2), (3, 2, 0))
    for (m, p, q) in shapes
        A, B = samples(F, m * p), samples(F, p * q)
        A, B = reshape(A, m, p), reshape(B, p, q)
        R = refmatmul(A, B)
        @test A * B == R                                       # default strategy via mul!
        for s in MATMUL_STRATEGIES
            C = fill(one(F), m, q)                             # overwritten, not accumulated
            @test matmul!(s, C, A, B) === C
            @test C == R
        end
        x = samples(F, p)
        @test A * x == refmatmul(A, x)
    end
    A, B, C = rand(rng, F, 6, 6), rand(rng, F, 6, 6), rand(rng, F, 6, 6)
    @test (A * B) * C == A * (B * C)
    Id = [i == j ? one(F) : zero(F) for i in 1:6, j in 1:6]
    @test A * Id == A && Id * A == A
    # mul!(C, A, B, α, β) = A B α + C β, with α, β Booleans or field elements.
    C0 = rand(rng, F, 6, 6)
    @test mul!(copy(C0), A, B, true, true) == A * B + C0
    @test mul!(copy(C0), A, B, true, false) == A * B
    @test mul!(copy(C0), A, B, false, true) == C0
    α, β = rand(rng, F), rand(rng, F)
    @test mul!(copy(C0), A, B, α, β) == refmul.(A * B, Ref(α)) + refmul.(C0, Ref(β))
    # views (strided, non-contiguous)
    Av, Bv = view(rand(rng, F, 9, 8), 1:2:9, 2:7), view(rand(rng, F, 6, 12), :, 1:3:12)
    @test Av * Bv == refmatmul(Av, Bv)
    for s in MATMUL_STRATEGIES
        @test matmul!(s, similar(Av, 5, 4), Av, Bv) == refmatmul(Av, Bv)
    end
    @test_throws DimensionMismatch matmul!(TableMatMul(), zeros(F, 2, 2), zeros(F, 2, 3), zeros(F, 2, 2))
end

# Larger products (J8b: the size sweep of bench/matmul_sizes.jl goes up to 2048): a long inner
# dimension, against ScalarMatMul(MulTable()), which is checked against Recursive above.
@testset "CLMulMatMul, larger sizes, $F" for F in (GF2_16, GF2_32, GF2_64, GF2_128)
    m, p, q = 300, 1100, 70
    A, B = rand(rng, F, m, p), rand(rng, F, p, q)
    R = matmul!(ScalarMatMul(MulTable()), similar(A, m, q), A, B)
    @test matmul!(CLMulMatMul(), similar(A, m, q), A, B) == R
    @test A * B == R
end

# FF-P2: for a vector or two columns and a large A (`clmul_by_columns`), CLMulMatMul works column
# by column without transposing A. Both paths are tested directly, whichever the rule picks, and
# through `matmul!` and `*`. Oracle: ScalarMatMul(MulTable()), checked above.
@testset "CLMulMatMul, few columns (FF-P2), $F" for F in (GF2_16, GF2_32, GF2_64, GF2_128)
    ref(A, B) = matmul!(ScalarMatMul(MulTable()), similar(A, size(A, 1), size(B, 2)), A, B)
    for (m, p) in ((300, 1100), (1, 50), (50, 1), (65, 3), (0, 4), (4, 0))
        A = rand(rng, F, m, p)
        x = rand(rng, F, p)
        p >= 3 && (x[1] = zero(F); x[end] = zero(F); x[2] = one(F))   # zero and unit entries
        R = vec(ref(A, reshape(x, p, 1)))
        c = fill(one(F), m)                                         # overwritten
        @test matmul!(CLMulMatMul(), c, A, x) === c
        @test c == R
        @test A * x == R
        for q in (1, 2, 3)
            B = q == 1 ? x : rand(rng, F, p, q)
            RB = q == 1 ? R : ref(A, B)
            if has_pclmul()
                for f! in (clmul_columns_add!, clmul_transposed_add!)
                    C = q == 1 ? fill(one(F), m) : fill(one(F), m, q)
                    @test f!(C, A, B) === C
                    @test C == RB .+ one(F)                          # adds to C
                end
            end
            q > 1 && @test matmul!(CLMulMatMul(), similar(A, m, q), A, B) == RB
        end
    end
    # the rule, at the shapes `bench/matvec.jl sizes` measured (src/bulk.md, "Matrix × vector")
    big = 1024 ÷ sizeof(F) * 512                     # entries of a 512 KiB matrix
    @test clmul_by_columns(F, big ÷ 512, 512, 1)
    @test !clmul_by_columns(F, big ÷ 512 - 1, 512, 1)
    @test !clmul_by_columns(F, 1024, 1024, 3)
    @test clmul_by_columns(F, 2048, 2048, 2) && clmul_by_columns(F, 256, 2^22 ÷ sizeof(F) ÷ 256, 2)
    @test !clmul_by_columns(F, 16, 2^22 ÷ sizeof(F) ÷ 16, 2)          # thin: transposed
    @test !clmul_by_columns(F, 255, 2^24, 2)
    # strided, non-contiguous A, x and c
    Ap = rand(rng, F, 41, 60)
    A, x = view(Ap, 2:2:40, 1:3:60), view(rand(rng, F, 45), 1:2:40)
    cp = rand(rng, F, 50)
    cp0 = copy(cp)
    c = view(cp, 1:2:40)
    R = vec(ref(collect(A), reshape(collect(x), :, 1)))
    @test matmul!(CLMulMatMul(), c, A, x) == R
    @test cp[2:2:50] == cp0[2:2:50] && cp[41:end] == cp0[41:end]     # the rest untouched
    @test A * x == R
    if has_pclmul()
        c = view(fill!(cp, zero(F)), 1:2:40)
        @test clmul_columns_add!(c, A, x) == R
    end
    # a large A takes the column path: only the accumulators (at most 48 bytes per row) are
    # allocated, no transposed copy of A
    m = 1024 ÷ sizeof(F) * 2
    @test clmul_by_columns(F, m, 512, 1)
    A, x, c = rand(rng, F, m, 512), rand(rng, F, 512), Vector{F}(undef, m)
    R = vec(ref(A, reshape(x, :, 1)))
    @test matmul!(CLMulMatMul(), c, A, x) == R
    has_pclmul() && @test (@allocated matmul!(CLMulMatMul(), c, A, x)) <= 48 * m + 512
end

@testset "CLMulMatMul without PCLMULQDQ" begin
    hw = FiniteFieldArithmetic.PCLMUL[]
    try
        FiniteFieldArithmetic.PCLMUL[] = false
        for F in (GF2_16, GF2_64, GF2_128)
            A, B = rand(rng, F, 5, 7), rand(rng, F, 7, 4)
            @test matmul!(CLMulMatMul(), similar(A, 5, 4), A, B) == refmatmul(A, B)
        end
    finally
        FiniteFieldArithmetic.PCLMUL[] = hw
    end
end

@testset "bitsliced vectors, $F" for F in LEVELS
    for n in (0, 1, 63, 64, 65, 200, 1031)
        a, b = samples(F, n), samples(F, n)
        A, B = BitslicedVector(a), BitslicedVector(b)
        @test A isa AbstractVector{F} && length(A) == n
        @test Vector(A) == a && collect(B) == b               # round trip
        n > 0 && @test A[1] == a[1] && A[end] == a[end]
        P = A .* B
        @test P isa BitslicedVector{F}
        @test Vector(P) == refmul.(a, b)
        @test Vector(A .+ B) == a .+ b
        C = BitslicedVector(zeros(F, n))
        @test mul_elementwise!(C, A, B) === C && Vector(C) == refmul.(a, b)
        if n > 0
            x = rand(rng, F)
            C[n] = x
            @test C[n] == x && Vector(C)[1:(n - 1)] == refmul.(a, b)[1:(n - 1)]
        end
        # the padding planes stay zero, so products of the padding never leak into the elements
        @test Vector(BitslicedVector(a) .* BitslicedVector(b)) == Vector(P)
    end
    @test_throws DimensionMismatch BitslicedVector(zeros(F, 3)) .* BitslicedVector(zeros(F, 4))
    @test mul_elementwise!(similar(samples(F, 5)), fill(one(F), 5), fill(one(F), 5)) == fill(one(F), 5)
end

@testset "BitslicedVector at GF(2^64) and GF(2^128) (J8b)" begin
    # the levels above GF(2^32) run their top recursion levels through memory: products of many
    # blocks, all elements checked against the reference, and no allocation proportional to n
    for F in (GF2_64, GF2_128), n in (256, 257, 3000)
        a, b = samples(F, n), samples(F, n)
        A, B = BitslicedVector(a), BitslicedVector(b)
        C = similar(A)
        @test Vector(mul_elementwise!(C, A, B)) == refmul.(a, b)
        @test (@allocated mul_elementwise!(C, A, B)) <= 64 * 1024     # one scratch buffer
    end
end

# --- J8b: packing by bit-matrix transposes (src/bulk.md, "Bitsliced vectors") ----------------
#
# Oracle: the transpose read off bit by bit.

using FiniteFieldArithmetic: transpose64!

@testset "64 × 64 bit-matrix transpose" begin
    getbit(x, r, c) = (x[r + 1] >> c) & 1
    for x0 in (rand(rng, UInt64, 64), zeros(UInt64, 64), fill(typemax(UInt64), 64),
               [UInt64(1) << r for r in 0:63], [UInt64(1) << (63 - r) for r in 0:63])
        x = copy(x0)
        @test transpose64!(x) === x
        @test all(getbit(x, r, c) == getbit(x0, c, r) for r in 0:63, c in 0:63)
        @test transpose64!(x) == x0                         # an involution
    end
end

@testset "packing from other vectors, $F" for F in (GF2, GF16, GF256, GF2_16, GF2_32, GF2_64,
                                                      GF2_128)
    a = samples(F, 300)
    @test Vector(BitslicedVector(view(a, 5:250))) == a[5:250]
    @test Vector(BitslicedVector(view(a, 300:-3:1))) == a[300:-3:1]
    P = BitslicedVector(a)
    @test all(P[i] == a[i] for i in eachindex(a))            # getindex agrees with unpacking
    @test (BitslicedVector(a); @allocated BitslicedVector(a)) <= 2 * sizeof(P.planes) + 1024
    out = similar(a, length(a))
    @test (Vector(P); @allocated Vector(P)) <= 2 * sizeof(out) + 1024
end

# --- J8b: the bitsliced matrix product (src/bitsliced_matmul.md) ------------------------------
#
# Sizes around the block boundaries of the GF(2) kernel (64 bits of the inner dimension per word,
# 256 columns per SIMD word), and a long inner dimension; the oracle is ScalarMatMul(MulTable()),
# itself checked against Recursive above. Structural checks: linearity in each factor.

@testset "BitslicedMatMul, block boundaries, $F" for F in LEVELS
    for (m, p, q) in ((1, 64, 256), (65, 129, 257), (2, 63, 255), (5, 1, 1), (64, 64, 64))
        A, B = rand(rng, F, m, p), rand(rng, F, p, q)
        R = matmul!(ScalarMatMul(MulTable()), similar(A, m, q), A, B)
        C = fill(one(F), m, q)
        @test matmul!(BitslicedMatMul(), C, A, B) == R
        x = rand(rng, F, p)
        @test matmul!(BitslicedMatMul(), similar(x, m), A, x) == refmatmul(A, x)
    end
    A1, A2, B = rand(rng, F, 9, 70), rand(rng, F, 9, 70), rand(rng, F, 70, 11)
    s = BitslicedMatMul()
    mm(X, Y) = matmul!(s, similar(X, size(X, 1), size(Y, 2)), X, Y)
    @test mm(A1 + A2, B) == mm(A1, B) + mm(A2, B)
    @test mm(permutedims(B), permutedims(A1)) == permutedims(mm(A1, B))   # (AB)ᵀ = BᵀAᵀ
end

@testset "BitslicedMatMul, larger sizes, $F" for F in LEVELS
    m, p, q = 300, 1100, 70
    A, B = rand(rng, F, m, p), rand(rng, F, p, q)
    R = matmul!(ScalarMatMul(MulTable()), similar(A, m, q), A, B)
    @test matmul!(BitslicedMatMul(), similar(A, m, q), A, B) == R
end

# --- J8g: the default by size (src/bitsliced_matmul.md, "Default by size") ---------------------
#
# `*` and `mul!` use BitslicedMatMul when every dimension of the product reaches the field's
# measured threshold, the field's previous default below. Oracle: the previous default, checked
# against Recursive above.

@testset "BySizeMatMul chooses by the smallest dimension" begin
    s = BySizeMatMul(TableMatMul(), BitslicedMatMul(), 10)
    @test choose_matmul(s, 10, 10, 10) === BitslicedMatMul()
    @test choose_matmul(s, 100, 10, 1000) === BitslicedMatMul()
    for (m, p, q) in ((9, 10, 10), (10, 9, 10), (10, 10, 9), (1000, 1000, 1))
        @test choose_matmul(s, m, p, q) === TableMatMul()
    end
    @test_throws ArgumentError BySizeMatMul(TableMatMul(), BitslicedMatMul(), 0)
end

@testset "default by size (J8g), $F" for F in LEVELS
    s = default_matmul_strategy(F)
    t = bitsliced_threshold(F)
    @test s isa BySizeMatMul && s.large === BitslicedMatMul() && s.threshold == t
    @test s.small === (degree(F) <= 8 ? TableMatMul() : CLMulMatMul())
    @test t >= 1
    for (m, p, q) in ((t, t, t), (t + 1, t, t + 3), (t - 1, t, t + 1), (t, t + 2, t - 1))
        A, B = rand(rng, F, m, p), rand(rng, F, p, q)
        R = matmul!(s.small, similar(A, m, q), A, B)
        @test A * B == R
        C0 = rand(rng, F, m, q)
        α, β = rand(rng, F), rand(rng, F)
        @test mul!(copy(C0), A, B, true, true) == R + C0
        @test mul!(copy(C0), A, B, α, β) == refmul.(R, Ref(α)) + refmul.(C0, Ref(β))
        x = rand(rng, F, p)                                   # matrix × vector: q = 1
        @test A * x == matmul!(s.small, similar(x, m), A, x)
    end
end

# --- Regressions for the open issues (MathStruct/FiniteFields#2, #3, #5) ----------------------

@testset "MulBy builds and owns its table (#2)" begin
    # The table is never accepted from outside: the generated (c, tab) constructor is gone, so an
    # undersized or wrong table cannot reach the unchecked lookups.
    @test_throws MethodError MulBy{GF256, UInt8}(GF256(3), zeros(UInt8, 1, 1))
    @test_throws MethodError MulBy{GF2_64, UInt64}(GF2_64(3), zeros(UInt64, 256, 8))
    for F in LEVELS
        m = MulBy(F(1))
        @test size(m.tab) == (256, sizeof(FiniteFieldArithmetic.storagetype(F)))
    end
end

# An RNG that writes all ones into a byte array and then fails.
struct FailingRNG <: Random.AbstractRNG end
function Random.rand!(::FailingRNG, A::Array{UInt8}, ::Random.SamplerType{UInt8})
    fill!(A, 0xff)
    error("RNG failure")
end

# A field element whose layout is not that of its storage integer (two bytes, storage UInt8).
struct Tagged <: FiniteFieldArithmetic.BinaryFieldElement
    b::UInt8
    tag::UInt8
end
FiniteFieldArithmetic.bits(x::Tagged) = x.b
FiniteFieldArithmetic.storagetype(::Type{Tagged}) = UInt8
FiniteFieldArithmetic.degree(::Type{Tagged}) = 8
FiniteFieldArithmetic.unsafe_frombits(::Type{Tagged}, b::UInt8) = Tagged(b, 0x5a)

@testset "bulk rand! keeps elements valid (#3)" begin
    A = fill(zero(GF4), 100)
    @test_throws ErrorException rand!(FailingRNG(), A)
    @test all(x -> bits(x) <= 0x03, A)                     # masked although the RNG threw
    @test FiniteFieldArithmetic.storage_layout(GF4) && FiniteFieldArithmetic.storage_layout(GF2_128)
    @test !FiniteFieldArithmetic.storage_layout(Tagged)
    T = rand!(Xoshiro(1), Vector{Tagged}(undef, 50))       # element-wise: every tag is set
    @test all(x -> x.tag == 0x5a, T)
    @test length(unique(bits.(T))) > 10
end

@testset "BitslicedVector broadcasts expand singletons (#5), $F" for F in (GF16, GF2_32, GF2_128)
    a, s = samples(F, 3), rand(rng, F)
    A, S = BitslicedVector(a), BitslicedVector([s])
    for (x, y, xv, yv) in ((A, S, a, [s]), (S, A, [s], a))     # both operand orders
        P, Q = x .* y, x .+ y
        @test P isa BitslicedVector{F} && Vector(P) == refmul.(xv, yv)
        @test Q isa BitslicedVector{F} && Vector(Q) == xv .+ yv
        C = BitslicedVector(zeros(F, 3))
        C .= x .* y                                         # broadcast assignment
        @test Vector(C) == refmul.(xv, yv)
        C .= x .+ y
        @test Vector(C) == xv .+ yv
    end
    @test Vector(S .* S) == [refmul(s, s)]
    E = BitslicedVector(F[])
    @test length(E .* S) == 0 && length(S .+ E) == 0
    @test_throws DimensionMismatch A .+ BitslicedVector(samples(F, 2))
end
