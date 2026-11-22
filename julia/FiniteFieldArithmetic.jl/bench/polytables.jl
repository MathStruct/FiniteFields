# J1a: the table strategies MulTable() (degree ≤ 8) and LogTable() (degree ≤ 16) for
# polynomial-basis fields against the carry-less product CLMul() and the inversion strategies
# ItohTsujii() and Euclid(). Chooses default_strategy / default_inv_strategy; recorded in
# src/polyfield.md, "Table strategies".
# Run: julia --project=julia/FiniteFieldArithmetic.jl/bench julia/FiniteFieldArithmetic.jl/bench/polytables.jl [degrees...]
using FiniteFieldArithmetic, BenchmarkTools, Random
using FiniteFieldArithmetic: mul, inverse, CLMul, MulTable, LogTable, ItohTsujii, Euclid

const L = 4096

function chain(s, x, y, n)              # latency: each product waits for the previous one
    for _ in 1:n
        x = mul(s, x, y) + y
    end
    return x
end
function inv_chain(s, x, y, n)
    for _ in 1:n
        x = inverse(s, x) + y
        iszero(x) && (x = y)
    end
    return x
end
mulall!(s, c, a, b) = (c .= mul.(Ref(s), a, b); c)
invall!(s, c, b) = (c .= inverse.(Ref(s), b); c)

ns(t) = round(t / L * 1e9; digits = 2)

degrees = isempty(ARGS) ? collect(1:16) : parse.(Int, ARGS)
fields = Any[("Conway GF(2^$n)", conway_field(n)) for n in degrees]
8 in degrees && push!(fields, ("AES GF(2^8)", GF256_AES))

println("Julia ", VERSION, ", ", Sys.CPU_NAME, "; ns per element, throughput over $L elements / latency chain")
println(rpad("field", 18), rpad("strategy", 12), rpad("mul thr", 10), rpad("mul lat", 10),
        rpad("inv thr", 10), "inv lat")
for (name, F) in fields
    rng = Xoshiro(1)
    a, b = rand(rng, F, L), rand(rng, F, L)
    b .= ifelse.(iszero.(b), one(F), b)
    c = similar(a)
    n = degree(F)
    strategies = Any[CLMul(), ItohTsujii(), Euclid()]
    n <= 16 && push!(strategies, LogTable())
    n <= 8 && push!(strategies, MulTable())
    for s in strategies
        ismul = s isa FiniteFieldArithmetic.MulStrategy
        mt = ismul ? ns(@belapsed mulall!($s, $c, $a, $b)) : "-"
        ml = ismul ? ns(@belapsed chain($s, $(a[1]), $(b[1]), L)) : "-"
        si = s isa CLMul ? nothing : s          # CLMul has no inverse of its own here
        it = si === nothing ? "-" : ns(@belapsed invall!($si, $c, $b))
        il = si === nothing ? "-" : ns(@belapsed inv_chain($si, $(b[1]), $(b[2]), L))
        println(rpad(name, 18), rpad(string(nameof(typeof(s))), 12), rpad(mt, 10), rpad(ml, 10),
                rpad(it, 10), il)
    end
end
