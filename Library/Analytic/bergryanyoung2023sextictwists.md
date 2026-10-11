---
bibkey: bergryanyoung2023sextictwists
authors: Jennifer Berg; Nathan C. Ryan; Matthew P. Young
year: 2023
title: "Vanishing of Quartic and Sextic Twists of L-functions"
doi: null
url: https://arxiv.org/abs/2301.05329v2
claim: "For quartic and sextic Dirichlet twist families, normalized Gauss-sum squares have different equidistribution rates in the full and totally-order subfamilies; composite even order mixes unitary and orthogonal aspects."
strata_touched: []
license: citation-only
triage: anchor
---

# Composite-even Gauss sums are mixed families

The source is [arXiv:2301.05329v2](https://arxiv.org/pdf/2301.05329v2),
updated 23 January 2023. It studies quartic and sextic twists of elliptic
curve $L$-functions and introduces totally quartic and totally sextic
subfamilies. This card records the structural boundary relevant to the
project; it is not a proof audit or Lean certification.

## The sextic boundary

The paper analyzes the equidistribution of squares of normalized sextic Gauss
sums. The full sextic family converges more slowly than its totally sextic
subfamily. The authors explain this through the composite-even order: the
full family has both unitary and orthogonal aspects, whereas restricting to
the totally sextic sector removes part of that mixture.

This is evidence that an order-six character cannot be treated as an
independent product of a quadratic and a cubic component after taking an
average. The component labels can alter the symmetry type and the rate of
equidistribution.

## Relation to the current contour gap

The project's complementary kernel contains a moving quadratic twist coupled
to a cubic Gauss factor. The sextic-twist analysis identifies exactly the
kind of composite-order correlation that must remain in a joint estimate:
one must retain the full component sector, or prove a valid decomposition
with its cross-correlation terms. Replacing the kernel by a product of
separate quadratic and cubic moments would therefore require a new
independence theorem and is not supplied by this source.

The paper concerns statistical central values of elliptic-curve twists. It
does not bound the project's signed kernel, prove the order-six residue
identity needed for (J), establish detector coverage, or imply Robin's
inequality or the Riemann hypothesis.

