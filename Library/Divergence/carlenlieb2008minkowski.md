---
bibkey: carlenlieb2008minkowski
authors: Eric A. Carlen and Elliott H. Lieb
year: 2008
title: A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II
doi: null
url: https://arxiv.org/abs/0710.4167v3
claim: Theorem 1.1 supplies fixed-congruence trace convexity at q=1 for exponents from one to two.
strata_touched:
  - D5/S3/Quantum/Hiai
license: citation-only
triage: anchor
---

# Fixed-congruence Carlen-Lieb supplier

For positive definite complex X, fixed invertible complex Z and 1 <= a <= 2,
the map X -> Re Tr((Z* X^a Z)^(1/a)) is convex. Z need not be selfadjoint;
both adjoints in the positive definite congruence are retained.
The empty finite matrix dimension gives the zero trace functional.

The connected proof uses operator power convexity on the whole positive
cone in arbitrary complete ordered complex C-star algebras. Its actual
all-Hilbert Jensen condition feeds the public generalized perspective
theorem. The existing Hilbert-Schmidt bridge at arbitrary real exponent
identifies the resulting trace perspective with
Re Tr(Z* X^a Z W^(1-a)).

Reverse trace Young gives the lower bound
a Re Tr((Z* X^a Z)^(1/a)) <= Re Tr(Z* X^a Z W^(1-a)) + (a-1) Re Tr W.
At each endpoint choose the explicit positive definite optimizer
W = (Z* X^a Z)^(1/a). Interpolate these two W in the positive definite
cone and apply joint trace perspective convexity, its affine trace
penalty and the Young bound at the mixture. Division by a > 0 gives
the claimed convexity. This is the classical variational proof, not
a novelty claim or the full Hiai Problem 5.18.

For the Hiai parameter range, set a=2p and take the same fixed invertible
Z from the inverse-mean variational formula. The required range
1/2 <= p < 1 gives 1 <= a < 2. The other curvature supplier is joint
concavity of the outer 1/p trace power of the congruence of the
weighted geometric mean of B^p and A^p; it is not supplied by this result.
The inverse-mean identity, full joint-convexity assembly and
support-constrained semidefinite limit also remain separate obligations.

The paper is cited; its prose or proof text is not transcribed. Physlib
and Mathlib source dependencies retain their respective Apache-2.0
attribution and source licenses.
