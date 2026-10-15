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
P_*=29{,}582{,}000{,}000{,}000,
$$

the source checks both exchange inequalities after clearing denominators by
exact integer arithmetic. It follows that every superabundant $n$ with
$P^+(n)>P_*$ satisfies

$$
\nu_p(n)\ge2\qquad(p\le7{,}608{,}793).
$$

Vega's lower bound on the largest prime factor of a hypothetical least Robin
counterexample among integers greater than 5040 places that source beyond
$P_*$, so the same cutoff is a necessary condition for such a counterexample.
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

## Finite Fibonacci-rank exclusion mask

The valuation conclusion supplies a finite necessary-condition filter for the
Fibonacci candidate family. In this section set $B=7\,608\,793$, distinct
from the largest-prime threshold $P_*$ above. Let $z(p)$ denote the least positive index with
$p\mid F_{z(p)}$, and define

$$
R_B=\{r\ge7:r\text{ is prime and }z(p)=r\text{ for some prime }p\le B\}.
$$

The congruence itself is the $p\mid V$ branch already recorded in FIB §205.3;
the new finite datum here is the cutoff-indexed set of prime ranks and its
enumeration under the external valuation certificate.

For every $r\in R_B$, choose such a witness $p$. Then $p\mid F_r$ gives

$$
1+F_rg\equiv1\pmod p,
$$

so $p\nmid1+F_rg$. Consequently no member of this rank class can satisfy
the external necessary condition $p^2\mid N$ at every prime $p\le B$.
Conditional on the block-exchange and least-counterexample hypotheses above,
the implication is therefore

$$
r\in R_B
\Longrightarrow
1+F_rg\text{ is not the globally least Robin counterexample}
$$

for every integer $g$ for which the candidate is in the stated range. This
does not rule out that an individual candidate violates Robin's inequality;
it only removes it from the least-counterexample search under the external
valuation certificate.

The exact enumeration in the companion experiment
[`research220-fib-rank-cutoff`](https://github.com/the-omega-institute/trureturing-experiments/tree/ad3e57ac/research220-fib-rank-cutoff)
finds $25\,370$ distinct prime ranks in $R_B$ for
$B=7\,608\,793$, with largest rank $3\,804\,397$. The output records a
witness prime and witness count for each rank; it is a finite computation and
does not assert that the complementary ranks are admissible or that the mask
extends beyond this cutoff.
For context, FIB §205.2 gives $p\ge2r-1$ for every prime divisor of
$F_r$ when $r\ge7$ is prime, so this cutoff can reach no rank above
$(B+1)/2=3\,804\,397$; the enumeration reaches that endpoint.

The same argument has an all-rank form. Write

$$
P_B=\prod_{p\le B}p,
\qquad
\mathcal A_B=\{r\ge1:\gcd(F_r,P_B)=1\}.
$$

Under the same least-counterexample hypothesis, every candidate
$N_{r,g}=1+F_rg$ must have $r\in\mathcal A_B$. Equivalently,

$$
r\in\mathcal A_B
\iff
z(p)\nmid r\quad\text{for every prime }p\le B.
$$

Thus the finite cutoff creates a rank sieve for the whole FIB address space;
the set $R_B$ above is its prime-rank slice. For example, the witnesses
$z(2)=3$, $z(3)=4$, and $z(5)=5$ already force
$3\nmid r$, $4\nmid r$, and $5\nmid r$ for any such least-counterexample
candidate. This is a necessary sieve only: membership in $\mathcal A_B$ does
not establish Robin for $1+F_rg$.

For the original multiplier window $g\in I_r$, the entire enumerated
prime-rank mask lies below Axler's existing finite range. Indeed,
$F_r<2^r$ gives

$$
\log(1+gF_r)<2r\le7\,608\,794
\qquad(r\in R_B,\ g\in I_r).
$$

By contrast, with $K=999999476056$ from Axler's Lemma 2.3,

$$
\log N_K\ge K\log2>K/2=499999738028.
$$

Thus every such integer greater than 5040 already satisfies Robin by that
lemma, independently of the block-exchange certificate. This comparison
is for the enumerated prime ranks and the stated bounded window; it does
not bound candidates with unrestricted $g$ or all composite ranks in
$\mathcal A_B$.

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
