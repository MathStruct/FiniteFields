using Test

@testset "FiniteFieldArithmetic" begin
    @testset "nimber fields" include("nimber.jl")
    @testset "nimber fields above GF(256)" include("nimber_large.jl")
    @testset "fast strategies for the large levels (J2a)" include("nimber_fast.jl")
    @testset "bulk and array operations (J8)" include("bulk.jl")
    @testset "constant times array in broadcasts (J8c)" include("constmul.jl")
    @testset "default strategy of inv" include("inv_default.jl")
    @testset "smallest field of an element (J9)" include("subfield.jl")
    @testset "polynomial-basis and Conway fields (J1a)" include("conway.jl")
    @testset "pseudo-Conway fields from On_2 (J1a)" include("pseudo_conway.jl")
    @testset "table strategies for small polynomial-basis fields (J1a)" include("polytables.jl")
    @testset "inversion strategies (J3)" include("inversion.jl")
    @testset "rank-encoded fields GF(2^n) in On_2 (J10)" include("nimfield.jl")
    @testset "printing" include("printing.jl")
    @testset "static checks" begin
        include("aqua.jl")
        include("jet.jl")
    end
end
