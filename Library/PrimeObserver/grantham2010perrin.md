---
bibkey: grantham2010perrin
authors: Jon Grantham
year: 2010
title: "There are infinitely many Perrin pseudoprimes"
doi: 10.1016/j.jnt.2009.11.008
claim: "Theorem 2.1 gives infinitely many Frobenius pseudoprimes for any monic squarefree integer polynomial. The construction in Theorem 5.3 produces Carmichael numbers all of whose prime factors split completely in the prescribed number field."
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed splitting fields and simultaneous pseudoprimes

Primary source: *Journal of Number Theory* 130 (2010), 1117–1128.
Author preprint: <https://arxiv.org/abs/1903.06825v1>.
The arXiv deposit is dated 2019; the journal result is from 2010.

Theorem 2.1 assumes a monic squarefree polynomial in `Z[X]` and its
splitting field `K`. The reduction immediately following it explains that
it suffices to construct Carmichael numbers whose every prime factor
splits completely modulo that polynomial. The proof of Theorem 5.3
constructs exactly such numbers from products of distinct completely
split primes and verifies Korselt's criterion.

The result is unconditional. Theorem 5.3 gives a lower bound
`x^(eta/3-epsilon)` for sufficiently large `x`, where `eta>0` and the
threshold depend on the field. It does not give a uniform estimate as
the field varies with the input size or with the number of test polynomials.

For a finite family of separable monic integer polynomials, use their
common splitting field and exclude the primes dividing their
discriminants. One way to enforce a finite exclusion set `S` is to adjoin
`zeta_m`, where `m=8 product_{q in S, q odd} q`: every prime in `S`
ramifies in this cyclotomic subfield and therefore cannot be a prime
that splits completely in the larger field. This is the application used
in observer theory §305, rather than an inference that arbitrary
Frobenius pseudoprimes have all elements fixed by exponentiation.

The earlier paper, “Frobenius Pseudoprimes,” *Mathematics of Computation*
70 (2001), 873–891, Proposition 6.1, explains the completely split
Carmichael mechanism. Its primary preprint is
<https://arxiv.org/abs/1903.06820v1>. It is not the infinitude proof.

The conclusion for a fixed family holds for all shifts. It gives no
superpolynomial lower bound on the first detecting k-bonacci order as a
function of the input bit length, and does not exclude input-dependent
growing families or separate primality certificates.
