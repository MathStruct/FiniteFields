# J10: products, inverses and embeddings in the rank-encoded fields Nim{n} (ADR-0005), against the
# Conway fields (J1a) and the nimbers of nearby degree. Recorded in src/nimfield.md.
# Run: julia --project=julia/FiniteFieldArithmetic.jl/bench julia/FiniteFieldArithmetic.jl/bench/nimfield.jl
using FiniteFieldArithmetic, BenchmarkTools, Random

const L = 4096
function chain(x, y, n)
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

println("Julia ", VERSION, ", ", Sys.CPU_NAME)
println(rpad("field", 24), rpad("mul thr", 10), rpad("mul lat", 10), rpad("inv thr", 10), "inv lat   (ns per element)")
fields = Any[]
for n in (3, 7, 12, 24, 33, 48, 63, 96, 107, 127)
    push!(fields, ("Nim GF(2^$n)", nim_field(n)))
    n in conway_degrees() && push!(fields, ("Conway GF(2^$n)", conway_field(n)))
end
append!(fields, [("nimber GF(2^8)", GF256), ("nimber GF(2^64)", GF2_64), ("nimber GF(2^128)", GF2_128)])
for (name, F) in fields
    rng = Xoshiro(1)
    a, b = rand(rng, F, L), rand(rng, F, L)
    b .= ifelse.(iszero.(b), one(F), b)
    c = similar(a)
    mt = @belapsed $c .= $a .* $b
    ml = @belapsed chain($(a[1]), $(b[1]), L)
    it = @belapsed $c .= inv.($b)
    il = @belapsed inv_chain($(b[1]), $(b[2]), L)
    println(rpad(name, 24), rpad(ns(mt), 10), rpad(ns(ml), 10), rpad(ns(it), 10), ns(il))
end

println()
println("embed, minimal_degree, ==, hash (per element, over $L elements)")
for (name, G, F) in (("Nim 3 → Nim 12", nim_field(12), nim_field(3)), ("GF16 → Nim 12", nim_field(12), GF16),
                     ("Nim 21 → Nim 126", nim_field(126), nim_field(21)),
                     # Conway ↔ rank encoding: isomorphisms, and mixed embeddings
                     ("Conway 12 → Nim 12", nim_field(12), conway_field(12)),
                     ("Nim 12 → Conway 12", conway_field(12), nim_field(12)),
                     ("Conway 63 → Nim 63", nim_field(63), conway_field(63)),
                     ("Nim 63 → Conway 63", conway_field(63), nim_field(63)),
                     ("Conway 127 → Nim 127", nim_field(127), conway_field(127)),
                     ("Nim 127 → Conway 127", conway_field(127), nim_field(127)),
                     ("Conway 21 → Nim 126", nim_field(126), conway_field(21)),
                     ("Nim 21 → Conway 126", conway_field(126), nim_field(21)),
                     ("GF16 → Conway 12", conway_field(12), GF16),
                     ("GF256 → Conway 24", conway_field(24), GF256),
                     ("Conway 21 → Conway 126", conway_field(126), conway_field(21)))
    a = rand(Xoshiro(2), F, L)
    c = Vector{G}(undef, L)
    t = @belapsed $c .= embed.($G, $a)
    println(rpad(name, 24), ns(t), " ns")
end
for n in (12, 126)
    a = rand(Xoshiro(3), nim_field(n), L)
    t = @belapsed foreach(x -> Base.donotdelete(minimal_degree(x)), $a)
    h = @belapsed foreach(x -> Base.donotdelete(hash(x)), $a)
    println(rpad("Nim $n minimal_degree", 24), ns(t), " ns;   hash ", ns(h), " ns")
end
