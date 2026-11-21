#implementation #characteristic-2 #construction #categorical

> Polynomial-basis fields $\mathbb{F}_2[x]/(f)$, $\deg f \le 128$ (backlog J1a, first part):
> `PolyElement{N, T, F}`, the **Conway fields** `conway_field(n)` from Lübeck's table (every
> $n \le 92$ and 21 degrees above, not 128), the AES and GHASH fields, `embed` between Conway
> fields, and isomorphisms between the Conway and nimber fields of degree $2^k \le 64$ that
> commute with the embeddings. Products by carry-less multiplication and Barrett reduction,
> inverses by the extended Euclidean algorithm.

> Sources: R. Lidl, H. Niederreiter, *Finite Fields* (2nd ed., 1997), Theorem 2.6 (subfields);
> that $\mathbb{F}_2[x]/(f)$ is a field for irreducible $f$ is mathlib's `AdjoinRoot.instField`
> (below).
> Conway polynomials: R. A. Parker's definition as given by W. Nickel and F. Lübeck,
> [Conway polynomials for finite fields](https://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/index.html)
> (definition and data). Barrett reduction of polynomials: V. Gopal et al., *Fast CRC
> Computation for Generic Polynomials Using PCLMULQDQ Instruction* (Intel, 2009); exactness
> proved below. AES: FIPS-197 (2001), Sec. 4.2. GHASH: NIST SP 800-38D (2007), Sec. 6.3.
> mathlib: [`AdjoinRoot.instField`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdjoinRoot.html#AdjoinRoot.instField)
> (`AdjoinRoot f` is a field for irreducible `f`); mathlib has no Conway polynomials. Not
> formalized here.
> code: `src/polyfield.jl`, `src/conway_table.jl` (generated, provenance in its header).
> tests: `test/conway.jl`. benchmark: `bench/polyfield.jl`.

## The type

`PolyElement{N, T, F}` is $\mathbb{F}_2[x]/(f)$ with $f = x^N + \sum_i F_i x^i$: the modulus is a
type parameter, so one type per field and the Barrett constant is a compile-time constant. The
element is its coefficient vector in the basis $1, x, \dots, x^{N-1}$, stored in the smallest
unsigned type with $N$ bits. The raw type does not check that $f$ is irreducible;
`poly_field(n, low)` does (Rabin's test) and returns the type. `conway_field(n)` is
`PolyElement{n, T, C_n - x^n}`, so `poly_field(8, 0x1d) === conway_field(8)`: a field given by
its Conway polynomial *is* the Conway field, there is no second type for it.

| name | modulus | storage |
|---|---|---|
| `conway_field(n)`, $n \in$ `conway_degrees()` | $C_n$ (Lübeck) | smallest `UInt` with $n$ bits |
| `GF256_AES` | $x^8 + x^4 + x^3 + x + 1$ | `UInt8` |
| `GF2_128_GHASH` | $x^{128} + x^7 + x^2 + x + 1$ | `UInt128` |
| `poly_field(n, low)` | any irreducible $x^n + \text{low}$, $n \le 128$ | smallest `UInt` |

GHASH note: GCM stores coefficients bit-reflected (the coefficient of $x^0$ is the most
significant bit of the first byte); `GF2_128_GHASH` uses bit $i$ = coefficient of $x^i$, so
`bitreverse` converts at the boundary. Not tested against a GCM vector.

Elements of different fields are never `==` (no promotion between polynomial bases or between
them and nimbers): maps are explicit, `embed(G, x)`.

## Conway polynomials

$C_n$ is the least (in Conway's order) monic primitive polynomial of degree $n$ over
$\mathbb{F}_2$ that is *compatible* with $C_m$ for every $m \mid n$:
$C_m\big(x^{(2^n-1)/(2^m-1)}\big) \equiv 0 \pmod{C_n}$. In characteristic 2 the signs in the
order do not matter and "least" means: the coefficients below $x^n$, read from $x^{n-1}$ down, are
least, i.e. $C_n - x^n$ is the least integer bit pattern.

The table is Lübeck's database (CPimport.txt, via the `sagemath/conway-polynomials` mirror;
sha256 and date in `src/conway_table.jl`), every entry with $p = 2$, $n \le 128$: 113 degrees, all
$n \le 92$, and not 93, 94, 99, 104–106, 111, 112, 116–118, 122–124, **128** (no Conway polynomial
of degree 128 is known to the database). The tests check, independently of the package code
(BigInt polynomials):

- every entry is irreducible (Rabin) and compatible with $C_m$ for every $m \mid n$ in the table;
- every entry with $n \le 64$ is primitive (factorisation of $2^n - 1$ by trial division, Pollard's
  rho, Miller–Rabin); above 64 primitivity is **not** checked;
- for $n \le 16$ the entry is the least such polynomial (exhaustive search).

**Categorically.** A Conway table is a functor from the divisibility poset
$(\mathbb{N}_{>0}, \mid)$ to fields, $m \mid n \mapsto (\alpha_m \mapsto \alpha_n^{(2^n-1)/(2^m-1)})$:
of the $m$ embeddings $\mathbb{F}_{2^m} \to \mathbb{F}_{2^n}$ it picks one per pair, coherently
(the composite $\mathbb{F}_{2^l} \to \mathbb{F}_{2^m} \to \mathbb{F}_{2^n}$ is the chosen
$\mathbb{F}_{2^l} \to \mathbb{F}_{2^n}$, since the exponents multiply). Its colimit is a concrete
$\overline{\mathbb{F}}_2$ (J7). `embed` is this functor on the degrees in the table; the
transitivity is tested ($\mathbb{F}_{16} \to \mathbb{F}_{256} \to \mathbb{F}_{2^{24}}$).

## Products: Barrett reduction

For $a, b$ of degree $< N$ the carry-less product $p = ab$ has degree $\le 2N - 2$. Write
$p = H x^N + L$ ($\deg L < N$, $\deg H \le N - 2$) and $x^{2N} = \mu f + \rho$
($\deg \mu = N$, $\deg \rho < N$). Then the quotient of $p$ by $f$ is
$A = \lfloor H\mu / x^N \rfloor$ and $p \bmod f = L + (A F \bmod x^N)$, where $F = f - x^N$.

*Proof.* Write $H\mu = A x^N + B$, $\deg B < N$. Then
$x^N (H x^N - A f) = H x^{2N} - (H\mu - B) f = H\rho + B f$, which has degree
$\le \max(2N - 2, 2N - 1) = 2N - 1$, so $H x^N - A f$ is a polynomial of degree $\le N - 1$:
$A$ is the quotient of $H x^N$ by $f$, and of $p$ too, since $\deg L < \deg f$. The remainder
$p - A f$ has degree $< N$, so it equals its low $N$ coefficients, $L + (A x^N + A F) \bmod x^N
= L + (AF \bmod x^N)$. $\square$

With $\mu = x^N + \mu'$: $A = H + \lfloor H\mu'/x^N \rfloor$. So a product costs three carry-less
products ($ab$, $H\mu'$, $AF$) of $N$-bit operands; for $N > 64$ each is a $128 \times 128$
Karatsuba product of three `PCLMULQDQ` (the last needs only its low word). $\mu'$ is computed
per type at compile time (`barrett_mu`, a `@generated` constant). The modulus is dense in
general (Conway polynomials are), so the sparse shift-and-fold reduction of the nimber `CLMul`
strategy does not apply.

The nimber `CLMul` strategy is the name of this one too (`mul(CLMul(), a, b)`); it is the only
strategy for polynomial-basis fields so far. Tables for small $n$ are the obvious next one
(see Measurements).

## Inverses

Since J3 (`src/inversion.md`): `inv` uses `default_inv_strategy`, `ItohTsujii()` for every
polynomial-basis field; `Euclid()` and `Fermat()` are available through `inverse`. (In the first
version of J1a, `inv` was Euclid in the next wider type, and Fermat at $N = 128$.)

## Nimbers and Conway fields

For $n = 2^k$ both representations exist. An isomorphism
$\varphi_k : \mathbb{F}_2[x]/(C_{2^k}) \to \text{Nimber}_k$ is fixed by the image $r_k$ of
$\alpha_{2^k}$, a root of $C_{2^k}$ in the nimber field; there are $2^k$ roots (one Frobenius
orbit). For the $\varphi_k$ to commute with the embeddings (Conway $\mathbb{F}_{2^{2^{k-1}}} \to
\mathbb{F}_{2^{2^k}}$ on one side, the nimber inclusion on the other) we need
$r_k^{\,2^{2^{k-1}} + 1} = r_{k-1}$. Of the roots $r^{2^i}$ exactly those with $2^{k-1} \mid i$
satisfy it, i.e. two, $r$ and its conjugate over level $k - 1$.

**Convention (chosen 2026-11-20; confirmed by the maintainer 2026-11-21):** $r_0 = 1$, and
$r_k$ is the *smaller integer* of the two compatible roots. This gives

| $k$ | field | $r_k$ |
|---|---|---|
| 0 | GF(2) | `0x1` |
| 1 | GF(4) | `0x2` |
| 2 | GF(16) | `0x4` |
| 3 | GF(256) | `0x61` |
| 4 | GF(2^16) | `0x5392` |
| 5 | GF(2^32) | `0x57010244` |
| 6 | GF(2^64) | `0x4b51cd3b38c26bf9` |

(Computed at load time by Cantor–Zassenhaus root finding, `find_root` of `src/nimber_fast.jl`,
then the Frobenius orbit; the tests check each $r_k$ is a root, compatible, and the smaller of
the two.) Level 7 (GF(2^128)) has no isomorphism: there is no $C_{128}$ in the table.

The maps are $\mathbb{F}_2$-linear, applied by byte tables as the nimber `CLMul` change of basis
(`PolyBasis(F, α)`). `embed(Nimber, x::Conway)` goes Conway$_{2^j}$ → nimber level $j$ → inclusion;
`embed(Conway_n, x::Nimber)` goes nimber inclusion into level $\log_2 n$ → $\varphi^{-1}$ when $n$
is a power of two, and through `nim_field(n)` otherwise (the isomorphisms with every rank-encoded
field, `nimfield.md`, "Conway fields", which agree with these for $n = 2^k$). The
tests check that every square commutes, that the maps are ring homomorphisms and mutually
inverse, and bijective up to GF(2^16) (exhaustively).

## Tests

`test/conway.jl`: the table checks above; products against the BigInt oracle on random
elements of every Conway field, exhaustively for $n \le 10$ (products and inverses); inverses
against Fermat for $n \le 64$, $x \cdot x^{-1} = 1$ above; $\alpha_n$ is a root of $C_n$ and
$\alpha_n^{2^n - 1} = 1$; AES vectors of FIPS-197 ($\{57\} \bullet \{83\} = \{c1\}$,
$\{57\} \bullet \{13\} = \{fe\}$, $\{53\}^{-1} = \{ca\}$) and all of `GF256_AES` against the oracle;
GHASH field against the oracle; `embed` as above for all pairs $m \mid n \le 72$ in the table;
`@inferred` products and inverses.

## Measurements

`bench/polyfield.jl`, one run, Julia 1.13.1, x86_64-linux, CPU reported as `graniterapids`,
`PCLMULQDQ` available, 2026-11-21. Throughput: `c .= a .* b` (`inv.(b)`) over 4096 random
elements; latency: a chain `x = x * y + y` (`x = inv(x) + y`). Nanoseconds per element. The VM's
run-to-run noise has been up to about 40% in earlier sessions (FF-P1); single run.

| field | mul thr | mul lat | inv thr | inv lat |
|---|---|---|---|---|
| nimber GF(2^8) | 0.41 | 1.78 | 0.30 | 1.76 |
| Conway GF(2^8) | 2.93 | 6.49 | 22.8 | 15.7 |
| AES GF(2^8) | 3.01 | 6.67 | 24.2 | 14.5 |
| nimber GF(2^16) | 1.37 | 4.24 | 0.74 | 7.76 |
| Conway GF(2^16) | 2.83 | 7.97 | 62.4 | 59.8 |
| nimber GF(2^32) | 6.12 | 6.98 | 6.18 | 33.4 |
| Conway GF(2^32) | 2.69 | 6.47 | 122 | 121 |
| nimber GF(2^64) | 18.9 | 17.2 | 42.5 | 47.3 |
| Conway GF(2^64) | 2.52 | 4.39 | 421 | 395 |
| nimber GF(2^128) | 40.5 | 42.8 | 112 | 118 |
| GHASH GF(2^128) | 8.36 | 10.8 | 3072 | 3076 |
| Conway GF(2^3), (2^7), (2^13), (2^33) | 2.7–2.9 | 6.9–8.2 | 3–128 | 6–125 |
| Conway GF(2^65), (2^127) | 9.1, 9.0 | 14.2, 13.4 | 413, 802 | 412, 810 |

| `embed` | ns per element |
|---|---|
| Conway 8 ↔ nimber GF(256) | 0.19 |
| Conway 64 ↔ nimber GF(2^64) | 1.85 |
| Conway 8 → Conway 64 | 335 |
| Conway 32 → Conway 64 | 357 |
| Conway 3 → Conway 69 | 1548 |

Reading:

- **Products** cost the same, about 2.5–3 ns, for every degree up to 64 (three `PCLMULQDQ`),
  and about 9 ns from 65 to 128 (Karatsuba, eight). From GF(2^32) up this is *faster than the
  nimber defaults*: 2.5 against 18.9 ns at degree 64, 8.4 (GHASH) against 40.5 at 128. The
  nimber `CLMul` strategy pays the change of basis on every product; a Conway or GHASH element
  is already in the polynomial basis. Below GF(2^32) the nimber tables win (0.4 against 2.9 ns
  at GF(256)). This is a measurement, not a proposal to change ADR-0004; it is a question for
  the maintainer (bulk work in a polynomial basis, converting at the boundary for 1.85 ns).
- **Inverses** were slow in this first version: Euclid one bit at a time (about $2N$ steps),
  400 ns at degree 64, and Fermat (3 µs) for GHASH. Since J3 the default is Itoh–Tsujii, 81 ns
  at degree 64 and 340 ns for GHASH (`src/inversion.md`).
- **Conway → Conway embeddings** first recomputed $\beta = \alpha_n^{(2^n-1)/(2^m-1)}$ (about $2n$
  products) and then did $m$ products per element (the rows above). Since 2026-11-21 (J1a, at the
  maintainer's request) `embed` goes through $\mathbb{F}_{2^n} \subset \mathbf{On}_2$ instead:
  the isomorphism onto `nim_field(m)`, the inclusion, the inverse isomorphism of degree $n$
  (`nimfield.md`, "Conway fields"), three byte-table maps and no per-pair tables. The Horner
  version stays as `embed_horner`, the test reference (`test/conway.jl`: agreement for every
  table pair $m \mid n$). Timings below.

### Conway → Conway through On_2

The `embed` section of `bench/polyfield.jl`, one run, Julia 1.13.1, x86_64-linux (CPU reported
as `emeraldrapids`), 2026-11-21, ns per element over 4096 elements:

| `embed` | through On_2 | `embed_horner` |
|---|---|---|
| Conway 8 → Conway 64 | 4.6 | 387 |
| Conway 32 → Conway 64 | 3.5 | 365 |
| Conway 3 → Conway 69 | 26.9 | 1 519 |
| Conway 21 → Conway 126 | 25.3 | 2 423 |
| Conway 63 → Conway 126 | 34.1 | 2 044 |

50–100 times faster. Remaining cost: three byte-table maps, one 8-bit lookup per byte of storage
each (degree 69 and 126 are stored in a `UInt128`, so 16 lookups of 16 bytes per map). The
nimber isomorphisms on the same run: 0.19–0.22 ns (degree 8), 2.2–2.3 ns (degree 64).
- During development the first version took **2.4 µs per product**: DispatchDoctor's `@stable`
  sees an argument of type `Type{P}` only as `DataType` and then checks the return type at
  runtime on every call. Helpers inside `@stable` take elements (or `Val`s), not types; JET
  caught it (`@test_opt` in `test/jet.jl`).
