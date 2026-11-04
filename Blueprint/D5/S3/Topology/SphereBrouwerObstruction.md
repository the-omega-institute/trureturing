# The Euclidean sphere cannot be contracted

## Abstract

The Euclidean sphere cannot be contracted.

**Theorem 1.1 (Noncontractibility from reduced singular homology).**

Lean statement: `D5/S3/Topology/SphereBrouwerObstruction.not_contractible_unit_sphere`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/SphereBrouwerObstruction.not_contractible_unit_sphere` (`✓ std3`). ∎

*Citation.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size, Question 3*. URL: <https://arxiv.org/abs/2608.13320v1>.

*Commentary.*

For every positive natural n, the unit sphere of real Euclidean n-space is not contractible. Ambient dimension one is included.

TauCeti computes the sphere's reduced singular homology with integer coefficients in degree n-1 and identifies it with the nonzero integer coefficient module. The upstream proof transports this computation from a Euclidean space of the same dimension, so its statement applies to every nontrivial finite-dimensional real normed space.

A contraction would make reduced singular homology zero in every degree. The sphere computation would then force the integer coefficient module to be zero, contradicting the fact that zero and one are distinct.

The endpoint is adopted from the exact TauCeti.not_contractibleSpace_sphere declaration by a source port, because the supplier and receiving Mathlib pins differ. The immutable source revision and path, TauCeti copyright, complete Apache-2.0 license, modification notices and own-pinned-Mathlib retirement condition are recorded in the linked Library note and port sources. The homology obstruction and lower-six result carry no novelty claim.

## References

- Truth anchor: `D5/S3/Topology/SphereBrouwerObstruction.not_contractible_unit_sphere`
