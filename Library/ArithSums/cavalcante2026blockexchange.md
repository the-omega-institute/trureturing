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
counterexample places that source beyond $B$, so the same cutoff is a
necessary condition for such a counterexample. The paper compares it with
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
Consequently this source can be reused only after a separately proved
common-source map from a FIB address to the full multiplicative factorization.
It strengthens the conditional least-counterexample filter, but it does not
pay the signed Robin tail or produce an RH proof.
