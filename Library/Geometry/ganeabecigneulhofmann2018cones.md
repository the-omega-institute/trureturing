---
bibkey: ganeabecigneulhofmann2018cones
authors: Octavian Ganea, Gary Becigneul, and Thomas Hofmann
year: 2018
title: Hyperbolic Entailment Cones for Learning Hierarchical Embeddings
doi: null
url: https://proceedings.mlr.press/v80/ganea18a.html
claim: The unit tangent hyperboloid geodesic has the classical cosh-sinh expression.
strata_touched:
  - D5/S3/Geometry/Hyperideal/ActualRaysJointAngle
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Geometry/ganeabecigneulhofmann2018cones -->
# Unit tangent rays on the hyperboloid

## Source and scope

The paper appears in Proceedings of Machine Learning Research 80,
1646-1655. Appendix A of its supplementary material defines the future
unit hyperboloid with time-first Lorentz signature and identifies its
tangent space by Lorentz orthogonality. Theorem 6, equation (38), gives
the unit-speed geodesic as x cosh(t) + v sinh(t), stated on [0,1].
It attributes the formula to Robbin and Salamon, equation (6.4.10).
The original supplement is available at
https://proceedings.mlr.press/v80/ganea18a/ganea18a-supp.pdf .

## Exact application boundary

The repository uses time-last coordinates and the previously defined
HyperbolicThreeSpace metric. The actual-ray construction verifies the
future-sheet inequality for every real parameter and identifies its
projection using the original lift, inverse-coordinate and cosh-distance
contracts. It does not assume an identification of Riemannian and metric
distances from the cited paper.

The joint comparison-angle limit is derived from these metric lines by
a removable-slope extension of sinh at zero. The supplement's Theorem 6
does not state that two-parameter limit or the repository's precise
projection contract. This attribution concerns the classical geodesic
formula, with no novelty claim for the underlying hyperbolic geometry.

## Verified locator

- Declared URL: https://proceedings.mlr.press/v80/ganea18a.html
- Primary supplementary PDF:
  https://proceedings.mlr.press/v80/ganea18a/ganea18a-supp.pdf
- Verified passage: Appendix A, Theorem 6, equation (38), PDF page 1.
  The unit-speed geodesic is stated on [0,1] and attributed there to
  Robbin and Salamon (2011), equation (6.4.10).
- Locator scope: the classical unit tangent geodesic formula. The global
  metric-ray construction and unrestricted joint comparison-angle limit
  are repository derivations within the exact application boundary above.
