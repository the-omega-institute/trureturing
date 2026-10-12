---
bibkey: cavalcante2026blockexchange
authors: Claudemir de Souza Cavalcante
year: 2026
title: A Block-Exchange Valuation Bound for Superabundant Numbers and Robin's Inequality
doi: 10.5281/zenodo.21725356
url: https://doi.org/10.5281/zenodo.21725356
claim: The paper gives an exact 92-versus-47 prime-block exchange that raises the uniform exponent-two cutoff for a hypothetical least Robin counterexample to 7,608,793; it remains a necessary condition and does not prove Robin's inequality or identify a FIB multiplicative source.
strata_touched: []
license: citation-only
triage: anchor
---

# Block exchange and the current valuation cutoff

The source is Claudemir de Souza Cavalcante, *A Block-Exchange Valuation
Bound for Superabundant Numbers and Robin's Inequality*, Zenodo record
[21725356](https://doi.org/10.5281/zenodo.21725356), 31 July 2026. The
deposited PDF is 9 pages and has SHA-256
`e792a805a09dc2f64b5a5fa2e198dc3a230b6fbe412a03c674c430c589c40c4b`.
This is a source-scope record, not an independent proof audit or Lean
verification.

## The exchange lemma

For a superabundant number

$$
n=\prod_{p\le P}p^{a_p},\qquad a_2\ge a_3\ge\cdots\ge a_P\ge1,
$$

suppose a supported prime $q$ has exponent one. Every supported prime at
least $q$ then has exponent one. The source exchanges $k$ consecutive primes
$u_i$ beginning at $q$ for $\ell$ larger supported primes $v_j$. If

$$
\prod_i u_i<\prod_jv_j,
$$

and

$$
\prod_i\left(1+\frac1{u_i(u_i+1)}\right)
\prod_j\frac{v_j}{v_j+1}>1,
$$

the exchanged integer is smaller and has larger abundancy, contradicting
superabundance.

## Exact supplied bound

Using $k=92$ consecutive primes beginning at $M=7{,}608{,}793$ and the
$\ell=47$ largest primes below

$$
B=29{,}582{,}000{,}000{,}000,
$$

the source checks both exchange inequalities after clearing denominators by
exact integer arithmetic. It follows that every superabundant $n$ with
$P^+(n)>B$ satisfies

$$
\nu_p(n)\ge2\qquad(p\le7{,}608{,}793).
$$

Vega's lower bound on the largest prime factor of a hypothetical least Robin
counterexample among integers greater than 5040 places that source beyond
$B$, so the same cutoff is a necessary condition for such a counterexample.
The paper compares it with
the earlier direct cutoff $5{,}438{,}903$ and with the collective-tail cutoff
$233{,}911$.

The fixed 92-versus-47 certificate is sharp only for that chosen block: its
abundancy comparison reverses when the starting prime is advanced to the next
prime. This is not a global optimality statement about all possible block
exchanges.

## Boundary for the FIB route

The argument is a local exchange in the multiplicative exponent vector. The
FIB five-state window is an additive Zeckendorf inclusion state; its symbols
do not provide $P^+(n)$, $\nu_p(n)$, or the superabundance hypothesis.
Necessary divisibility filters can nevertheless use the existing modular
observations of the same finite source. A complete Robin comparison still
requires the actual multiplicative data and its signed remainder.

## Application through the existing FIB CRT interface

The [FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
§205.4, already combines forced divisors of $N_{r,g}=1+F_rg$ into one CRT
class and counts that class in a multiplier interval. §207.3 already records
the complete-core inverse candidate and the conditions for actual
realization. Reuse those interfaces with the valuation cutoffs above and
the [collective-tail cutoffs](cavalcante2026collectivetail.md), setting

$$
M=\prod_{p\le61}p^4
  \prod_{61<p\le479}p^3
  \prod_{479<p\le7\,608\,793}p^2.
$$

For a prime index $r\ge7$, put $V=F_r$ and
$I_r=[\lceil V/10\rceil,\lfloor V/5\rfloor]\cap\mathbb Z$.
**Conditional on accepting both external valuation results**, if, for some
$g\in I_r$, the integer $N_{r,g}>5040$ is the globally least Robin
counterexample in that range, then $M\mid N_{r,g}$. The existing CRT
interface therefore requires

$$
\gcd(V,M)=1,\qquad g\equiv-V^{-1}\pmod M.
$$

If the gcd condition fails there are no such candidates. Otherwise the
number satisfying this necessary congruence in $I_r$ is at most
$\lfloor(|I_r|-1)/M\rfloor+1$. In particular $|I_r|\le M$ leaves at most
one candidate. The same source has $N_{r,g}\le1+V^2/5$, so $M\mid N_{r,g}$
also requires $V^2\ge5(M-1)$. These exact integer conditions avoid treating
rounded rank scales as certified boundaries.

This is a parameter application of existing CRT and size comparisons,
not a new estimate. Its low-rank scales are already inside the finite
Robin ranges recorded in [Axler's Lemma 2.3](../notes/axler2023robin.md)
and, conditional on its external certificates, the
[Polak verification](../Analytic/polak2026finiterobinca.md), also applied
to this family in FIB §258.2. It adds no Robin-safe range. Excluding an
integer from being the globally least counterexample does not establish
Robin for that integer; neither does retaining a congruence candidate
establish a violation. No independent complete proof audit of either
Cavalcante source or Lean verification of this application is claimed.
