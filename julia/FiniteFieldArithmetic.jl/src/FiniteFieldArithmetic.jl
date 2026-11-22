"""
    FiniteFieldArithmetic

Arithmetic in finite fields, characteristic 2 first. Implemented so far: the nimber fields
``\\mathbb{F}_2 \\subset \\mathbb{F}_4 \\subset \\dots \\subset \\mathbb{F}_{2^{128}}``
([`GF2`](@ref), [`GF4`](@ref), [`GF16`](@ref), [`GF256`](@ref), [`GF2_16`](@ref),
[`GF2_32`](@ref), [`GF2_64`](@ref), [`GF2_128`](@ref)), nested as integers.

Multiplication strategies ([`MulStrategy`](@ref): [`Recursive`](@ref), [`MulTable`](@ref),
[`LogTable`](@ref), [`LogTable16`](@ref), [`CLMul`](@ref)) are reached through [`mul`](@ref) and
[`inverse`](@ref); `*` uses [`default_strategy`](@ref), `inv` (and `/`)
[`default_inv_strategy`](@ref). Inversion strategies for every representation
([`InvStrategy`](@ref): [`Fermat`](@ref), [`ItohTsujii`](@ref), [`Euclid`](@ref);
`src/inversion.md`).

Bulk operations (`src/bulk.md`): fast `rand!` for arrays, [`MulBy`](@ref) (multiplication by a
constant), matrix products ([`matmul!`](@ref) with a [`MatMulStrategy`](@ref), among them
[`BitslicedMatMul`](@ref) (`src/bitsliced_matmul.md`); `*` and
`LinearAlgebra.mul!` use [`default_matmul_strategy`](@ref)), [`BitslicedVector`](@ref), and the
strategies of `c .* a` ([`ConstMulStrategy`](@ref), chosen by [`default_constmul_strategy`](@ref)).

Polynomial-basis fields ``\\mathbb{F}_2[x]/(f)`` (`src/polyfield.md`): [`PolyElement`](@ref),
the Conway fields ([`conway_field`](@ref)), [`GF256_AES`](@ref), [`GF2_128_GHASH`](@ref), and
[`embed`](@ref) between Conway fields and between Conway and nimber fields.

The canonical fields ``\\mathbb{F}_{2^n} \\subset \\mathbf{On}_2`` for every ``n \\le 128``
(ADR-0005, `src/nimfield.md`): [`nim_field`](@ref), [`Nim`](@ref), with `Nimber` for ``n = 2^k``.

The smallest field of an element (`src/subfield.md`): [`minimal_level`](@ref),
[`minimal_degree`](@ref), [`reduce_field`](@ref).

Type stability of the arithmetic is enforced by DispatchDoctor's `@stable` (mode `"error"`); set
the preference `instability_check = "disable"` for this package to switch the checks off.
"""
module FiniteFieldArithmetic

using DispatchDoctor: @stable
using LinearAlgebra: LinearAlgebra
using Random: Random

export BinaryFieldElement, Nimber, GF2, GF4, GF16, GF256, GF2_16, GF2_32, GF2_64, GF2_128
export characteristic, degree, elements
export minimal_level, minimal_degree, reduce_field
export MulBy, BitslicedVector
export PolyElement, poly_field, conway_field, conway_degrees, conway_generator, is_conway
export pseudo_conway_field, pseudo_conway_degrees, is_pseudo_conway
export GF256_AES, GF2_128_GHASH, embed
export Nim, nim_field

include("binaryfield.jl")
include("nimber.jl")
include("nimber_fast.jl")
include("bulk.jl")
include("bitsliced_matmul.jl")
include("subfield.jl")
include("polyfield.jl")
include("inversion.jl")
include("nimfield.jl")

end
