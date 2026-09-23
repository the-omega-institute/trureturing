---
bibkey: simon2007equilibrium
authors: Barry Simon
year: 2007
title: "Equilibrium Measures and Capacities in Spectral Theory"
doi: null
url: https://arxiv.org/abs/0711.2700v1
claim: "Theorems 1.10 and 1.11 and Appendix A, Equation (A.8), give regular-measure norm asymptotics and the capacity of an interval."
strata_touched:
  - D5/S3/Constants/Moments/CatalanSquareHankelLimits
license: citation-only
triage: anchor
---

# Simon's regular-measure route to the same rate

## Verified locator

The supplied primary-source audit read https://arxiv.org/abs/0711.2700v1 and
identifies Theorem 1.10(i), the Erdos-Turan criterion in Theorem 1.11, and
Appendix A, Equation (A.8). The first relates regularity to the asymptotic
norms of monic orthogonal polynomials. The second makes a measure regular on
an interval when its density is positive almost everywhere there. Equation
(A.8) gives the ordinary logarithmic capacity of an interval; for `[0,16]`
it is `4`.

Applied to the positive product density from Lin's route, multiplication by
`z^r` for `r=1,2` preserves positivity almost everywhere on `(0,16)` and
therefore preserves regularity. The standard monic Gram determinant identity
then expresses each shifted Hankel determinant as the product of the squared
monic orthogonal-polynomial norms. Summing their logarithmic asymptotics gives
`log D_r(n)/n^2 -> log 4 = 2 log 2` for both shifts.

## Scope

This is an attributed ordinary classical corollary of the cited results, not
a claim that Simon states A277829 or A278770. The repository proof is a
separate elementary argument: it constructs explicit Gram models and matching
Chebyshev upper and lower estimates without taking regular-measure theory as a
Lean premise. The theorem locators are inherited from the supplied source
audit; this metadata pass did not independently reread the paper.
