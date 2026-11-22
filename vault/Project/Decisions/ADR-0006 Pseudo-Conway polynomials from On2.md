#design #characteristic-2 #construction

> **Status:** accepted (2026-11-21, maintainer: "Go with option B. … I would like to have the
> choices that afford more structure, over the ones that don't or are arbitrary."). For the 15
> degrees $n \le 128$ that Lübeck's table lacks, a polynomial-basis field
> `pseudo_conway_field(n)` with a primitive generator whose norms are the Conway generators of
> the subfields, defined from $\mathbf{On}_2$ by a deterministic rule.

> Implementation: `julia/FiniteFieldArithmetic.jl/src/polyfield.md`, "Pseudo-Conway fields";
> data `src/pseudo_conway_table.jl` from `research/nimber_closure/pseudo_conway.jl` and
> `research/nimber_closure/mersenne_factors.py`. Builds on
> [[ADR-0005 Rank encoding of GF(2^n) in Conway's On2]].

## Context

The Conway fields (J1a) give a polynomial basis with fast products (2.5–11 ns, against 19–58 ns
for `Nim`) and a primitive generator $\alpha_n$ with Conway's compatibility
$\alpha_n^{(2^n-1)/(2^m-1)} = \alpha_m$, so discrete logarithms agree across the subfield lattice.
Lübeck's table has no $C_n$ for $n = 93, 94, 99, 104, 105, 106, 111, 112, 116, 117, 118, 122,
123, 124, 128$. As far as we know (not checked against Lübeck's notes) the obstacle is finding the
*lexicographically least* compatible primitive polynomial: compatibility fixes the norms to the
subfields, so few polynomials qualify (about one in $2^{64}$ for $n = 128$) and an ordered search
does not end. `nim_field(n)` already covers these degrees canonically, without that structure.

## Options considered

- **A. Pseudo-Conway polynomials as in Sage** (after Heath–Loehr): primitive and compatible, but
  found by random choices. Arbitrary; rejected for the reason StandardFF was (ADR-0005).
- **B. Defined from $\mathbf{On}_2$** (chosen): in $\mathbb{F}_{2^n} \subset \mathbf{On}_2$ let
  $\beta$ be the primitive element of least rank, $k \ge 1$ the least exponent with
  $\gcd(k, 2^n - 1) = 1$ and $(\beta^k)^{(2^n-1)/(2^m-1)} = \rho_m$ for every $m \mid n$ ($\rho_m$ the
  image of $\alpha_m$, [[ADR-0005 Rank encoding of GF(2^n) in Conway's On2]] and `nimfield.md`,
  "Conway fields"); $\rho_n = \beta^k$ and $P_n$ its minimal polynomial.
- **C. No new polynomials:** expose the internal basis of `nim_field(n)`. Canonical but without a
  primitive, compatible generator: less structure.

## Decision

Option B. The name stays distinct (`pseudo_conway_field`, `is_pseudo_conway`), since a Conway
polynomial computed later would in general differ; `embed` and `conway_generator` treat Conway and
pseudo-Conway fields alike ("the compatible system").

## Consequences

- Every $n \le 128$ has a polynomial-basis field in the compatible system, and every one is
  isomorphic to `nim_field(n)` by $\alpha_n \mapsto \rho_n$; GF(2^128) now has one too.
- The rule depends only on the order of $\mathbf{On}_2$, the Conway polynomials and the choice
  "least β, then least k". Taking the least-rank *compatible* primitive element instead would be
  the closer analogue of Conway's rule but is infeasible for the same reason as the Conway search.
- Computing $k$ needs discrete logarithms in $\mathbb{F}_{2^m}$ for the maximal divisors $m$
  (Pohlig–Hellman; Pollard rho for the prime $2^{61} - 1$, needed by $n = 122$) and the
  factorisations of $2^n - 1$ (GNU `factor`, checked with `sympy.isprime`); done once, offline.
- "Least rank" for β is cheap: the ranks below $2^{2^j}$ ($2^j$ the largest proper power of
  two dividing $n$) form the nimber subfield, which has no primitive element, and the least
  primitive rank above that is small. For $n = 128$ it is $2^{64} + 2$.
- The tests recheck everything from the data: irreducibility, primitivity (the prime list is
  shown to exhaust $2^n - 1$), compatibility with each $C_m$ evaluated directly, and the rule
  itself (β least, k least) in `nim_field(n)`.
