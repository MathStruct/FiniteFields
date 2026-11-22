#overview

> Handoff for the next session: where the work stands, what is next, and what is open. A session
> that starts reads it after `AGENTS.md`; a session that ends updates it. Replace stale text
> rather than appending; history belongs in git.

**Last updated:** 2026-11-22, on branch **`dev-danielb`** (the working branch; pushed).
`plan/agents-handoff` is merged into it and no longer used.

## Stage

Implementation of approved items. Approved and done so far: J0, the nimber fields GF(2) …
GF(2^128), J2a, J8 (maintainer, 2026-11-19: "please implement J8!"), J8c (2026-11-19: "I
kinda want all three"), J8d (2026-11-20: "go with your J8d proposal, fix the GF(2^16)
slowdown first"), J8e (2026-11-20: "Switch to the tables"), J2b, the default for `inv`
(2026-11-20: "Please implement the next item!", taken as approval of item 1 of the then "Next"
list), **J8b** (2026-11-20: "Please implement the next item!" again, taken the same way;
packing, cache blocking measured, bitsliced matrix product and vectors done, the rest open) and
**J8g** (2026-11-20: "yes. once you benchmarked it somewhat it should become the default by
matrix size!"), **FF-P2** (2026-11-20: "Go ahead with it!"), **J9** (2026-11-20: asked "What
is the next item? Please implement!", then chose J9 when asked which) and **J1a** (2026-11-21:
"Please implement the next item!", then chose J1a, Conway fields, when asked which) and **J3**
(2026-11-21: "Why is J3 not approved? I would say I approve it!"), **ADR-0005 and R1**
(2026-11-21: "Approve ADR-0005 and R1, go ahead with step 2"), **J10 and R2** (2026-11-21:
"J10 & R2 approved!"), and the Lean connection to CombinatorialGames' `Nimber` (2026-11-21: "I'd
say approved. If the proof is not in mathlib but some other lean library use it!"), **R3**
(2026-11-21: "lean proof approved! Add it to the backlog.", then "Yes, go ahead with R3!"), and the
**J10 `embed` with the Conway fields** (2026-11-21: "Yes, go ahead with the J10 embed!"), Conway →
Conway through On_2 (2026-11-21), **pseudo-Conway fields, option B / ADR-0006** (2026-11-21: "Go
with option B"), the **J1a table strategies for small degrees** (2026-11-22: "Please implement the
next item!", taken as item 1 of the then "Next" list, within the approved J1a), and option (c), the AES/GHASH isomorphisms, approved at low priority. Ask before
starting a backlog section the maintainer has not approved.

## Done last

- **Pseudo-Conway fields from On_2** ([[ADR-0006 Pseudo-Conway polynomials from On2]], 2026-11-22):
  `pseudo_conway_field(n)`, `pseudo_conway_degrees()`, `is_pseudo_conway` for the 15 degrees
  missing from Lübeck's table (93 … 128). In GF(2^n) ⊂ On_2: β is the least-rank primitive
  element, $\rho_n = \beta^k$ with $k$ the least exponent prime to $2^n - 1$ whose norms are the
  Conway generators of the subfields, and $P_n$ is the minimal polynomial of $\rho_n$. So
  every $n \le 128$ has a polynomial-basis field with a primitive generator compatible across
  subfields, and GF(2^128) now has an isomorphism with the nimbers. `embed` and
  `conway_generator` treat Conway and pseudo-Conway fields alike.
  Data `src/pseudo_conway_table.jl` from `research/nimber_closure/pseudo_conway.jl` (about 1 min;
  Pohlig–Hellman, with Pollard rho for $2^{61} - 1$) and `mersenne_factors.py` (GNU `factor` plus
  `sympy.isprime`). Verified: `test/pseudo_conway.jl` (1 931 tests: irreducibility, primitivity
  with a prime list shown to exhaust $2^n - 1$, $C_m(x^e) = 0$ evaluated directly, the rule
  recomputed in `nim_field(n)`, isomorphisms, embeddings against `embed_horner`, JET); full
  `Pkg.test()` passes (2 636 022 tests, Aqua, JET). Not verified: CI, Julia 1.10; Lübeck's current data, which may
  have true $C_n$ for some of these degrees (his site is not on the network allowlist).

- **J1a: Conway → Conway `embed` through On_2** (2026-11-21, maintainer: "Confirmed, and yes, wire
  Conway → Conway through On_2!"): $\psi_n^{-1} \circ$ inclusion $\circ\, \psi_m$, three
  byte-table maps; 3.5–34 ns per element against 365 ns – 2.4 µs for the Horner embedding
  (`src/polyfield.md`). The Horner code is kept as `embed_horner`, the test reference
  (agreement for every table pair $m \mid n$). Nimber → Conway of degree $2^k$ is now the
  nimber inclusion plus one map. Verified: full `Pkg.test()` passes (2 634 078 tests, Aqua,
  JET). Not verified: CI, Julia 1.10.
  The root rule for the Conway ↔ rank isomorphisms and decision 0(a) are confirmed (below).

- **J10: `embed` between `nim_field` and the Conway fields** (2026-11-21; `src/nimfield.jl`, note
  `src/nimfield.md`, "Conway fields"; data `src/nim_conway_roots.jl` from
  `research/nimber_closure/conway_roots.jl`). Isomorphisms `conway_field(n)` ≅ `nim_field(n)` for
  all 113 table degrees: $\alpha_n \mapsto \rho_n$, the root of $C_n$ in
  $\mathbb{F}_{2^n} \subset \mathbf{On}_2$ compatible with every $\rho_m$ ($m \mid n$) and of least
  rank. That reproduces the provisional nimber convention (a) for $n = 2^k$ (so the nimber maps
  are unchanged) and extends it; confirmed by the maintainer. Number of
  compatible roots found = $n / \operatorname{lcm}\{m \mid n, m < n\}$ for every $n$, as predicted.
  `embed(nim_field(n), x::Conway_m)` and `embed(Conway_n, x::Nim/Nimber)` for $m \mid n$, by
  byte tables; Nimber → Conway of non-power-of-two degree now goes through `nim_field(n)` too.
  Verified: full `Pkg.test()` passes (2 631 022 tests, Aqua, JET incl. `@test_opt` on the new
  paths): root conditions recomputed for every $n$, homomorphisms, inverse maps, bijective for
  $n \le 12$, all commuting squares for table pairs $m \mid n$. Measured: 0.6 ns (degree 12) to 11 ns
  (degree 127) per isomorphism, against 2.4 µs for the Horner Conway embedding 21 → 126
  (`src/nimfield.md`). Not verified: CI, Julia 1.10.

- **GitHub issues #2–#5 and the failing Julia CI on `main`** (2026-11-21). CI: the `Julia min`
  job failed at `setup-julia` ("Unable to locate project file with project input: ."), because
  `version: min` reads `[compat]` from the repository root; `julia.yml` now passes
  `project: <package>`. #2: `MulBy` has only an inner constructor that builds its table. #3: bulk
  `rand!` takes the pointer path only when the element type is laid out as its storage integer
  (`storage_layout`), and masks in a `finally`. #4: `elements(F)` is an iterator (`Elements{F}`)
  with `SizeUnknown` from GF(2^64) on (`length` throws `OverflowError`). #5: `.*`/`.+` of
  `BitslicedVector`s expand a length-1 operand. Regression tests in `test/bulk.jl` and
  `test/nimber.jl`. Verified: `nimber.jl`, `bulk.jl` and `constmul.jl` pass locally on Julia 1.13.1,
  and the #4 tests fail on the old code; the full `Pkg.test()` (Aqua, JET included) passes,
  2 622 620 tests. Not verified: CI, Julia 1.10.
  #6 (matmul crossovers by shape) is still open: it needs benchmarks, not a fix.
- **R3: tower digits = binary digits, DiMuro's Lemma 1.1** (`lean/FiniteFields/NimberTower.lean`,
  note [[Rank encoding is order-preserving]], new section): for a tower of generators
  $g_j = {*}2^{a_j}$ satisfying `IsTower` (rings, `X ^ u_j ≤ leastNoRoots`, each above the tower
  below), the nim-monomial $g_k^{e_k} \cdots g_1^{e_1} {*}2^i$ is ${*}2^{a_k e_k + \dots + i}$
  (`mono_eq`, via CombinatorialGames' `IsRing.pow_mul_eq`); that exponent is strictly increasing in
  the lexicographic tower-digit order; so a basis reduced echelon for tower digits (as R1 computes)
  gives an order-preserving rank (`elem_lt_of_rank_lt`). `isTower_F4` shows the hypotheses are
  satisfiable. No `sorry`, standard axioms only (`#print axioms`), `lake build` passes.
  Not formalized: that R1's concrete towers satisfy `IsTower` (DiMuro Thm 3.1, Lenstra's
  $\alpha_u$; not approved). Checked by reading the code: R1's digit index (`On2.jl` header,
  `rank_encoding.jl` `digit`/`topdigit`: flat index $\sum e_j \cdot \text{stride}_j$, top generator
  largest stride, then the scalar bit) is the lexicographic order of the Lean statement.
  Not verified: Lean CI (`lean.yml`).

- **R2 on CombinatorialGames' `Nimber`** (`lean/FiniteFields/NimberDigits.lean`): binary digits of
  ordinals; nim-addition = symmetric difference of digits, ordinal order = colex of digits, and the
  rank encoding is order-preserving for any reduced echelon family of nimbers
  (`nimSum_lt_of_rank_lt`); no `sorry`, standard axioms only, `lake build` passes. New Lean
  dependency CombinatorialGames `061f2c9` (last commit on v4.36.0; builds against our mathlib tag).
  Policy recorded: other Lean libraries before own definitions (`AGENTS.md`, `Lean and mathlib`).
  Not formalized: existence of echelon bases (tower digits: R3, above).
  Not verified: the Lean CI run (`lean.yml`) with the new dependency.

- **J10: `nim_field(n)` for every $n \le 128$** (`src/nimfield.jl`, note `src/nimfield.md`, data
  `src/nim_data.jl` generated from R1, tests `test/nimfield.jl`, benchmark `bench/nimfield.jl`):
  `Nimber` for $n = 2^k$, `Nim{n, T}` otherwise, elements stored as ranks; products 3.6–58 ns
  (Conway + three byte-table maps); `embed`, `==`, `hash`, promotion across all degrees through
  $\mathbf{On}_2$; `minimal_degree`/`reduce_field`. Verified: `Pkg.test()` passes (2 622 552 checks,
  Aqua, JET), including agreement with the R1 data for every degree.
- **R2: the order-preservation proof** ([[Rank encoding is order-preserving]]) and its combinatorial
  step in Lean (`lean/FiniteFields/RankEncoding.lean`, no `sorry`; `lake build` passes).
- **Not verified:** CI (`lean.yml`, `julia.yml`, Full CI), other Julia versions; the jldoctests.

- **R1 and ADR-0005: the rank encoding of every $\mathbb{F}_{2^n} \subset \mathbf{On}_2$**
  ([[ADR-0005 Rank encoding of GF(2^n) in Conway's On2]], accepted; results in
  [[Canonical extension of the nimbers]], "Results of R1"; code and data in
  `research/nimber_closure/`). Lenstra's $\alpha_u$ computed for every prime $u \le 127$
  (the 13 of his table reproduced from scratch, 17 new, e.g. $\alpha_{47} = \chi_{23} + 1$,
  $\alpha_{107} = \chi_{53} + 1$); rank-encoding data (internal generator, minimal polynomial,
  change of basis, all inclusions) for $n = 1 \dots 128$ ($n = 107$, tower degree 884 676, took an hour). Checks pass: Lenstra's table, base-field
  independence, irreducibility, rank = nimber for $n = 2^k$, inclusions are compatible ring
  homomorphisms, and rank = ordinal position by brute force for 13 small fields.
  Not done: the order-preservation proof is a sketch (R2); no library type yet (J10); nothing in
  Lean. The package itself is unchanged.

- **Research: a canonical extension of the nimbers to every $\mathbb{F}_{2^n}$** (maintainer
  2026-11-21: rejected StandardFF for its pseudo-random choices, asked for a canonical structure;
  "Do that!"). Note [[Canonical extension of the nimbers]], scripts in
  `research/nimber_closure/`. Result: Conway's $\mathbf{On}_2$ below $\omega^{\omega^\omega}$
  (DiMuro, arXiv:1108.0962, after Lenstra 1977); Lenstra's table of $\alpha_u$ ($u \le 43$)
  verified with our nimber arithmetic; only $\mathbb{F}_{2^{2^k}}$ are initial segments, but
  the **rank of an element in ordinal order** is a canonical, linear $n$-bit encoding equal to
  the nimber value for $n = 2^k$. Needed and unknown: the excesses for the 17 primes 47 … 127.
  Nothing in the library changed.

- **J3, inversion strategies** (`src/inversion.jl`, note `src/inversion.md`, tests
  `test/inversion.jl`, benchmark `bench/inversion.jl`): `Fermat()`, `ItohTsujii()` (Frobenius
  powers as byte tables built per field at compile time, an unrolled `@generated` chain),
  `Euclid()` (first step removes $x^n$, so no wider type and also degree 128; nimbers through
  the `CLMul` basis from GF(2^16) up). Default `inv` for polynomial bases is now `ItohTsujii`
  (2–3× Euclid; GHASH 3.1 µs → 340 ns); nimber defaults unchanged (faster than all three).
  Verified: `Pkg.test()` passes, JET `@test_opt` on all strategies. Not verified: CI, other Julia
  versions; the two explanations of the timings in the note are labelled unprofiled.

- **J1a, first part: polynomial-basis and Conway fields** (`src/polyfield.jl`, note
  `src/polyfield.md`, data `src/conway_table.jl`, tests `test/conway.jl`, benchmark
  `bench/polyfield.jl`). `PolyElement{N, T, F}` = $\mathbb{F}_2[x]/(x^N + F)$ for $N \le 128$;
  `poly_field(n, low)`; `conway_field(n)` for the 113 degrees $\le 128$ in Lübeck's table (not
  128); `GF256_AES`, `GF2_128_GHASH`; `embed` between Conway fields ($m \mid n$) and between
  Conway and nimber fields of degree $2^k \le 64$. Products: carry-less multiplication plus
  Barrett reduction (exactness proved in the note). Inverses: extended Euclid (Fermat at 128).
  A small refactor: `PolyBasis(F, α)` in `src/nimber_fast.jl` takes the root.
- **Measured** (`src/polyfield.md`): Conway products 2.5–3 ns up to degree 64, 9 ns above;
  *faster than the nimber defaults from GF(2^32) up* (2.5 vs 18.9 ns at 64; GHASH 8.4 vs 40.5 at
  128), slower below (2.9 vs 0.4 ns at GF(256)). Inverses slow (400 ns at 64, 3 µs GHASH).
  Nimber ↔ Conway 0.2–1.9 ns per element; Conway → Conway 335 ns – 1.5 µs.
- **Verified:** `Pkg.test()` passes (Julia 1.13.1, x86_64-linux), incl. Aqua and JET
  (`@test_opt` on products/inverses of six polynomial fields). Table: every entry irreducible
  and compatible with its divisors, primitive for $n \le 64$, the least such polynomial for
  $n \le 16$ (independent BigInt oracle). Products against the oracle on every Conway field,
  exhaustive up to $n = 10$; FIPS-197 AES vectors.
- **Not verified:** primitivity of the table entries above degree 64 (needs factorisations of
  $2^n - 1$); a GCM test vector for `GF2_128_GHASH` (bit order differs, documented); other Julia
  versions; CI; the jldoctest of `conway_field` (no Documenter run).

Before that: J9 (smallest field of a nimber), FF-P2 (`CLMulMatMul` for matrix × vector), J8b
(inlining `LazyMulBy`), J8g (`BitslicedMatMul` the default by size), the bitsliced matrix
product and vectors at GF(2^64)/GF(2^128).
Earlier: J8b cache blocking (measured, not adopted), J8b packing by bit-matrix transposes, J2b,
J8e and J8d, J8c, J8, J2a, nimber GF(2) … GF(2^128), ADR-0004, `AGENTS.md`, CI, the move to
MathStruct. Details in git and the Backlog's *Done*.

## Next

Within the approved J1a (Backlog, "J1a — Representations, remaining"): bulk operations for
`PolyElement` can go ahead (Conway → Conway embeddings by byte tables, pseudo-Conway fields and
table strategies for small degrees: done). Approved at low priority: option (c), all $n$
isomorphisms between any `poly_field` (AES, GHASH) and the compatible system, with `embed`
using the one of least rank. Within J8b only ARM `PMULL` and GPU kernels remain
(not doable in this container).

Within the approved J3 (Backlog, "J3 — remaining"): division by Euclid directly, a faster
Euclid, bulk inversion (Montgomery's trick).

Not approved (need the maintainer's go): **J9b** (smallest field for Conway fields; now possible,
J1a exists); **J8f**; a cache-blocked transpose in `CLMulMatMul`; faster small bitsliced products;
**FF-P1**; **J1b** (arbitrary $n$, above 128); linear algebra (V5). Seen earlier, not measured:
in the scalar GF(2^16) `LazyMulBy` loop the size of the global `NIM256_MUL` table is reloaded
every element.

## Decisions in force (maintainer, 2026-11-19)

- (2026-11-21) **Prefer the choices that give more structure over those that do not or are
  arbitrary** ("I would like to have the choices that afford more structure, over the ones that
  don't or are arbitrary"). Cryptography is a low priority.
- (2026-11-21) Pseudo-Conway polynomials from On_2: [[ADR-0006 Pseudo-Conway polynomials from On2]].

- (2026-11-21, "Confirmed") Conway ↔ rank-encoded isomorphisms: $\alpha_n \mapsto$ the root of $C_n$
  in $\mathbb{F}_{2^n} \subset \mathbf{On}_2$ compatible with all $\alpha_m$, $m \mid n$, of least
  rank; for $n = 2^k$ the smaller-integer root $r_k$ (former open decision 0(a)).

- Purpose: theory, cryptanalysis, and learners built on finite fields; no cryptographic
  implementations, constant time not a goal.
- Characteristic 2 first; byte-sized fields first ($\mathbb{F}_2$, $\mathbb{F}_{2^8}$ … $\mathbb{F}_{2^{128}}$),
  then arbitrary $n$ (J1b) and $\overline{\mathbb{F}}_2$ (J7).
- Representations: [[ADR-0004 Nimbers as the default representation of GF(2^n)]].
- Strategies: tables and computed variants side by side, the default chosen by benchmark.
- Printing: hexadecimal always; `show` adds the field when it does not fill its storage.
- Layout `julia/FiniteFieldArithmetic.jl/`; `lake-manifest.json` and `flake.lock` committed; CI
  path-filtered plus the `full-ci` branch; mathlib upstreaming case by case; milestones deferred.

## Environment notes

- 2026-11-21: the **FiniteFields** environment now also allows `arxiv.org`, `export.arxiv.org`,
  `www.math.leidenuniv.nl`, `pub.math.leidenuniv.nl`, `en.wikipedia.org`, `oeis.org` (for the
  research note; added in this session). Lenstra, *On the algebraic closure of two* (1977) was
  not found there; his *Nim multiplication* (IHES/M/78/211) is at `pub.math.leidenuniv.nl/~hwl/PUBLICATIONS/1978a/art.pdf`.
- Cloud sessions: use the personal environment **FiniteFields** (allows `release.lean-lang.org`,
  `releases.lean-lang.org`, `cache.mathlib.org`, `pkg.julialang.org`). Start sessions with
  `MathStruct/FiniteFields` as the source; this session still pushes through GitHub's redirect from
  the old `DanielBoigk/FiniteFields` URL.
- No system Julia in the container: `nix develop .#julia -c julia ...` fetches Julia 1.13.1.
  The bench environment uses `[sources]` (Julia ≥ 1.11).
- On 2026-11-20 the session's network refused `pkg.julialang.org` (registry update failed); tests
  and benchmarks still ran from the packages already in `~/.julia`. A new dependency would need
  the **FiniteFields** environment.

## Open questions for the maintainer

00. **Next:** within the approved J10, faster `minimal_degree`/`hash` and bulk operations for
   `Nim` remain (Backlog). Within J1a: bulk operations for `PolyElement`, and (low priority) the AES/GHASH isomorphisms, option (c).
   Not approved: Lean proofs of the concrete relations ($\omega^3 = 2$, Lenstra's $\alpha_u$);
   J9b for Conway fields.
0. **J1a decisions taken provisionally (2026-11-21), please confirm or change:**
   (a) *confirmed 2026-11-21, see "Decisions in force"*; (b) no implicit
   promotion or `==` between fields: maps only through `embed`; (c) names `PolyElement`,
   `poly_field`, `conway_field`, `embed`, `GF256_AES`, `GF2_128_GHASH`; (d) the Conway data is
   Lübeck's, taken from the GPL-3 `sagemath/conway-polynomials` mirror (provenance and sha256 in
   `src/conway_table.jl`); the polynomials are mathematical facts, but say if you want the
   licensing checked or a different source; (e) Conway/polynomial-basis products are 4–7× faster
   than the nimber defaults from GF(2^32) up (measurement in `src/polyfield.md`): does that
   change anything in ADR-0004 for bulk work?
1. **Learners on finite fields:** when you are ready, write the ideas down (a research-question
   note in `vault/Research Questions/`), so the arithmetic API can be checked against them.
2. **GitHub Pages:** check that the repository's Pages setting serves the `gh-pages` branch.
3. **`main`:** merged on 2026-11-19 at the maintainer's request (fast-forward to `40cd1c2`, J2a).
   That push should run `julia.yml`, `lean.yml` and `pages.yml`; their results could not be
   read from the session (no GitHub API access), so check the Actions tab and the site.
4. **Milestones** (deferred).

## Known issues

- `lake build` warns that `lean/FiniteFields.lean` should start with `module` (mathlib uses the
  module system). Adopt it with the Lean layout (L0).
- Wikilinks use two styles (`[[Decisions/…]]` and `[[Project/Decisions/…]]`); move to by-name links
  with V0.
