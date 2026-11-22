#implementation #characteristic-2 #construction #categorical

> Polynomial-basis fields $\mathbb{F}_2[x]/(f)$, $\deg f \le 128$ (backlog J1a, first part):
> `PolyElement{N, T, F}`, the **Conway fields** `conway_field(n)` from Lübeck's table (every
> $n \le 92$ and 21 degrees above, not 128), the AES and GHASH fields, `embed` between Conway
> fields, and isomorphisms between the Conway and nimber fields of degree $2^k \le 64$ that
> commute with the embeddings. Products by carry-less multiplication and Barrett reduction, and
> by tables up to degree 16 (`MulTable`, `LogTable`, the defaults there); inverses by tables up to
> degree 16, Itoh–Tsujii above.

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
> tests: `test/conway.jl`, `test/polytables.jl`. benchmarks: `bench/polyfield.jl`,
> `bench/polytables.jl`.

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

The nimber `CLMul` strategy is the name of this one too (`mul(CLMul(), a, b)`); it is the default
from degree 17 up. Below, tables are faster (next section).

## Table strategies

For degree $N \le 16$ (J1a, "table strategies for small Conway fields"; 2026-11-22) the nimber
strategy names `MulTable()` and `LogTable()` also apply to polynomial-basis fields:

- `mul(MulTable(), a, b)`, `inverse(MulTable(), a)`, $N \le 8$: a product table of $2^{2N}$
  entries indexed by `(a << N) | b` (a vector, not a matrix, so no size is reloaded; 64 KiB at
  $N = 8$) and an inverse table of $2^N$ entries.
- `mul(LogTable(), a, b)`, `inverse(LogTable(), a)`, $N \le 16$: $ab = g^{\log a + \log b}$,
  $a^{-1} = g^{(2^N - 1) - \log a}$, with a logarithm table of $2^N$ entries (`UInt8` up to degree
  8, `UInt16` above) and an exponential table of $2(2^N - 1)$ entries, so that the sum of two
  logarithms needs no reduction (384 KiB at $N = 16$); zero by a branch.
- Above those degrees both throw `ArgumentError`.

**The base $g$** (`log_generator(F)`) is the primitive element with the least bit pattern. For
a Conway (or pseudo-Conway) field that is $x = \alpha_n$, since $x$ is primitive and the only
smaller nonzero pattern is $1$; so the table *is* the Conway discrete logarithm, the logarithm of
the compatible system ($\log_{\alpha_n} y = \frac{2^n-1}{2^m-1}\log_{\alpha_m} y$ for
$y \in \mathbb{F}_{2^m}$, $m \mid n$, by the compatibility). For a field where $x$ is not
primitive the least primitive pattern is the canonical choice: `0x03` for `GF256_AES` ($x$ has
order 51), and likewise for the internal bases of `nim_field`. Tested: primitive, and no smaller
pattern is (`test/polytables.jl`).

The tables are built per field from the carry-less product (`clmul_pow`, never `*`, which may
itself be a table lookup) by `@generated` functions that embed them as constants, at the first
call; the Itoh–Tsujii tables are built the same way (`src/inversion.jl`).

**Defaults** (`default_strategy`, `default_inv_strategy`, by degree): `MulTable()` up to 8,
`LogTable()` 9 … 16, `CLMul()` / `ItohTsujii()` above. Chosen by throughput, as for the nimbers
(J2b), from the measurements below. Since the rank-encoded fields `nim_field(n)` multiply and
invert in their internal polynomial basis, they use these tables too for $n \le 16$.

`bench/polytables.jl`, one run, Julia 1.13.1, x86_64-linux (CPU reported as `emeraldrapids`),
2026-11-22. Throughput over 4096 random elements (`c .= mul.(s, a, b)`, `c .= inverse.(s, b)`);
latency: chains `x = mul(s, x, y) + y`, `x = inverse(s, x) + y`. ns per element.

| field | `CLMul` mul thr / lat | `MulTable` mul thr / lat | `LogTable` mul thr / lat | `ItohTsujii` inv thr / lat | `Euclid` inv thr / lat | `MulTable` inv thr / lat | `LogTable` inv thr / lat |
|---|---|---|---|---|---|---|---|
| Conway 2^2 | 3.65 / 7.85 | 0.34 / 2.64 | 0.65 / 0.37 | 0.34 / 0.33 | 3.54 / 3.98 | 0.28 / 0.28 | 0.50 / 0.51 |
| Conway 2^4 | 3.15 / 7.86 | 0.34 / 2.73 | 0.84 / 3.94 | 6.49 / 15.1 | 9.97 / 11.1 | 0.36 / 0.61 | 0.52 / 1.21 |
| Conway 2^7 | 2.63 / 7.65 | 0.36 / 2.49 | 0.77 / 3.95 | 10.9 / 26.9 | 25.1 / 16.5 | 0.34 / 1.74 | 0.50 / 3.31 |
| Conway 2^8 | 3.65 / 8.02 | 0.35 / 5.87 | 0.79 / 3.73 | 13.7 / 41.2 | 26.8 / 16.2 | 0.36 / 2.01 | 0.52 / 3.40 |
| AES 2^8 | 2.86 / 7.15 | 0.45 / 5.40 | 0.79 / 3.96 | 17.5 / 39.1 | 25.4 / 17.6 | 0.36 / 2.11 | 0.52 / 3.94 |
| Conway 2^9 | 3.52 / 9.34 | – | 0.82 / 3.93 | 14.3 / 38.4 | 33.9 / 25.4 | – | 0.56 / 3.36 |
| Conway 2^12 | 3.65 / 9.12 | – | 0.73 / 3.94 | 31.3 / 59.3 | 49.7 / 31.0 | – | 0.56 / 4.00 |
| Conway 2^13 | 3.52 / 7.78 | – | 0.78 / 3.10 | 23.1 / 48.4 | 53.7 / 58.9 | – | 0.45 / 4.00 |
| Conway 2^15 | 3.52 / 9.08 | – | 1.06 / 7.50 | 28.4 / 52.3 | 55.4 / 54.4 | – | 0.76 / 7.99 |
| Conway 2^16 | 3.52 / 8.86 | – | 1.16 / 8.42 | 34.4 / 60.7 | 72.3 / 61.5 | – | 0.70 / 8.65 |

(Every degree 1 … 16 was run; the rows left out lie between their neighbours. In degree 1 and 2,
Itoh–Tsujii is almost free: the chain is empty or one squaring.) Reading:

- **Products:** `MulTable` 8–10× the throughput of `CLMul` up to degree 8, `LogTable` 3–5× up to 16.
  Latency is mixed (`MulTable` 2.1–2.7 ns at degree 1–7 and 5.9 at 8, `LogTable` 0.3–4 ns,
  each ahead at some degrees); the throughput decides, as before. Conway GF(256) by `MulTable`,
  0.35 ns, is now level with the nimber GF(256) (0.41 ns in the older run below, another CPU).
- **Latency of `MulTable` at degree 8** (5.9 ns, against 2.5–2.7 at degree 3–7) is likely the
  64 KiB table exceeding the 48 KiB L1 data cache in the random chain; not profiled.
- **`LogTable` from degree 14 up** gets slower (latency 5.8–8.4 ns), likely as the tables
  (96–384 KiB) leave L1 and L2 share; not profiled. Still faster than `CLMul` in both measures.
- **Inverses:** one lookup (or two), 0.3–0.8 ns throughput, against 3–34 ns for Itoh–Tsujii and
  4–72 ns for Euclid: 10–50×.

## Inverses

Since J3 (`src/inversion.md`): `inv` uses `default_inv_strategy`, `ItohTsujii()` for every
polynomial-basis field of degree above 16, the tables below (Table strategies); `Euclid()` and `Fermat()` are available through `inverse`. (In the first
version of J1a, `inv` was Euclid in the next wider type, and Fermat at $N = 128$.)

## Pseudo-Conway fields

[[ADR-0006 Pseudo-Conway polynomials from On2]] (maintainer, 2026-11-21, option B). For the 15
degrees $n \le 128$ without $C_n$ in the table (`pseudo_conway_degrees()`: 93, 94, 99, 104, 105,
106, 111, 112, 116, 117, 118, 122, 123, 124, 128), `pseudo_conway_field(n)` is
$\mathbb{F}_2[x]/(P_n)$ with $P_n$ defined in $\mathbb{F}_{2^n} \subset \mathbf{On}_2$:

1. $\beta$ = the primitive element of least rank;
2. $k$ = the least $k \ge 1$ with $\gcd(k, 2^n - 1) = 1$ and
   $(\beta^k)^{(2^n-1)/(2^m-1)} = \rho_m$ for every $m \mid n$, where $\rho_m$ is the image of the
   Conway generator $\alpha_m$ (`nimfield.md`, "Conway fields"; every proper divisor of a missing
   degree is a table degree);
3. $\rho_n = \beta^k$, and $P_n$ = its minimal polynomial.

So $x$ is primitive and $x^{(2^n-1)/(2^m-1)}$ is a root of $C_m$: Conway's compatibility, without
Conway's "lexicographically least". `is_conway` is false for these fields, `is_pseudo_conway` true;
`conway_generator`, `embed` (Conway ↔ pseudo-Conway, ↔ `nim_field`, ↔ nimbers for $n = 128$)
treat both kinds alike, with $\alpha_n \mapsto \rho_n$ as the isomorphism with `nim_field(n)`.

**Computing $k$.** $N_m(\beta)$ is primitive in $\mathbb{F}_{2^m}$, so
$N_m(\beta) = \rho_m^{\ell_m}$ with $\ell_m$ a unit mod $2^m - 1$, and the condition reads
$k \equiv \ell_m^{-1} \pmod{2^m - 1}$; for the maximal proper divisors $m$ it implies the others
(the norms compose and the $\rho_m$ are compatible). The $\ell_m$ are discrete logarithms in
`conway_field(m)` to base $\alpha_m$ (Pohlig–Hellman over the factorisation of $2^m - 1$;
baby-step giant-step for prime factors below $2^{42}$, Pollard rho with an $r$-adding walk above,
needed only for $2^{61} - 1$); the congruences are combined by the Chinese remainder theorem
(moduli not coprime, consistent by the compatibility of the $\rho_m$) to a class mod
$M = \operatorname{lcm}(2^m - 1)$, and $k$ is its least element prime to $2^n - 1$.
Factorisations of $2^n - 1$: GNU `factor`, each factor checked with `sympy.isprime`
(`research/nimber_closure/mersenne_factors.py`, `data/mersenne_factors.txt`).

**Finding β.** Let $2^j$ be the largest power of two dividing $n$ with $2^j < n$. The ranks
below $2^{2^j}$ are the nimber subfield $\mathbb{F}_{2^{2^j}}$, an initial segment of
$\mathbf{On}_2$ (rank = value there), so none of them is primitive and the search starts at
$2^{2^j}$. This matters for $n = 128$, whose ranks below $2^{64}$ are all of GF(2^64): there
$\beta = 2^{64} + 2$. A search from rank 1 would never have finished, and the first run of the
script did not.

**The run** (2026-11-22, one core): 1 s or less per degree, except $n = 122$, 44 s: one
discrete logarithm in GF(2^61), whose multiplicative group has prime order $2^{61} - 1$, by
Pollard rho in $3.6 \cdot 10^9$ steps. The ranks of $\beta$ are small (4 to 65 792, and
$2^{64} + 2$ for 128). The exponents $k$ run from $6 \cdot 10^{11}$ to $1.5 \cdot 10^{19}$.

**Data:** `src/pseudo_conway_table.jl` (per $n$: the bits of $P_n - x^n$, the rank of $\rho_n$, the
rank of $\beta$, $k$; and the primes dividing $2^n - 1$), generated by
`research/nimber_closure/pseudo_conway.jl`.

**Tests** (`test/pseudo_conway.jl`): $P_n$ irreducible (Rabin); the prime list exhausts $2^n - 1$
and passes Miller–Rabin (24 bases); $x$ has order $2^n - 1$; $C_m(x^{(2^n-1)/(2^m-1)}) = 0$ for
every table $m \mid n$, evaluated in the field itself (independent of $\mathbf{On}_2$); the rule
recomputed in `nim_field(n)`: the image of $x$ is the tabulated $\rho_n = \beta^k$, every smaller
rank than $\beta$ is not primitive, every smaller $k' \equiv k \pmod M$ shares a factor with
$2^n - 1$; isomorphisms with `nim_field(n)` (homomorphism, inverse); embeddings from Conway fields
agree with `embed_horner`; degree 128 against the nimbers GF(2^128); `@inferred`, JET.

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

The table below predates the table strategies (degree ≤ 16 is faster now: Table strategies).

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
