# J1a: products and inverses in the polynomial-basis fields (Conway fields, AES, GHASH) against
# the nimber fields of the same degree, and the cost of embed. Recorded in src/polyfield.md.
# Run: julia --project=julia/FiniteFieldArithmetic.jl/bench julia/FiniteFieldArithmetic.jl/bench/polyfield.jl
using FiniteFieldArithmetic, BenchmarkTools, Random
using FiniteFieldArithmetic: has_pclmul

const L = 4096

function chain(x, y, n)                 # latency: each product waits for the previous one
    for _ in 1:n
        x = x * y + y
    end
    return x
end
function inv_chain(x, y, n)
    for _ in 1:n
        x = inv(x) + y
        iszero(x) && (x = y)
    end
    return x
end

ns(t) = round(t / L * 1e9; digits = 2)

println("Julia ", VERSION, ", ", Sys.CPU_NAME, ", PCLMULQDQ: ", has_pclmul())
println(rpad("field", 30), rpad("mul thr", 10), rpad("mul lat", 10), rpad("inv thr", 10), "inv lat   (ns per element)")
fields = Any[]
for n in (8, 16, 32, 64)
    push!(fields, ("nimber GF(2^$n)", (GF256, GF2_16, GF2_32, GF2_64)[trailing_zeros(n) - 2]))
    push!(fields, ("Conway GF(2^$n)", conway_field(n)))
end
append!(fields, [("Conway GF(2^$n)", conway_field(n)) for n in (3, 7, 13, 33, 65, 127)])
append!(fields, [("AES GF(2^8)", GF256_AES), ("nimber GF(2^128)", GF2_128),
                 ("GHASH GF(2^128)", GF2_128_GHASH)])
for (name, F) in fields
    rng = Xoshiro(1)
    a, b = rand(rng, F, L), rand(rng, F, L)
    c = similar(a)
    b .= ifelse.(iszero.(b), one(F), b)
    mt = @belapsed $c .= $a .* $b
    ml = @belapsed chain($(a[1]), $(b[1]), L)
    it = @belapsed $c .= inv.($b)
    il = @belapsed inv_chain($(b[1]), $(b[2]), L)
    println(rpad(name, 30), rpad(ns(mt), 10), rpad(ns(ml), 10), rpad(ns(it), 10), ns(il))
end

println()
println("embed, per element (throughput over $L elements)")
for (name, G, F) in (("Conway 8 → nimber GF(256)", GF256, conway_field(8)),
                     ("nimber GF(256) → Conway 8", conway_field(8), GF256),
                     ("Conway 64 → nimber GF(2^64)", GF2_64, conway_field(64)),
                     ("nimber GF(2^64) → Conway 64", conway_field(64), GF2_64),
                     ("Conway 8 → Conway 64", conway_field(64), conway_field(8)),
                     ("Conway 32 → Conway 64", conway_field(64), conway_field(32)),
                     ("Conway 3 → Conway 69", conway_field(69), conway_field(3)),
                     ("Conway 21 → Conway 126", conway_field(126), conway_field(21)),
                     ("Conway 63 → Conway 126", conway_field(126), conway_field(63)))
    a = rand(Xoshiro(2), F, L)
    c = Vector{G}(undef, L)
    t = @belapsed $c .= embed.($G, $a)
    if is_conway(F) && is_conway(G)          # Conway → Conway: also the Horner reference
        h = @belapsed $c .= FiniteFieldArithmetic.embed_horner.($G, $a)
        println(rpad(name, 30), ns(t), " ns   (Horner ", ns(h), " ns)")
    else
        println(rpad(name, 30), ns(t), " ns")
    end
end
