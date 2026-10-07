# Continuous simplex self-maps have fixed points

## Abstract

Continuous simplex self-maps have fixed points.

**Theorem 1.1 (Continuous simplex self-maps have fixed points).**

Lean statement: `D5/S3/Geometry/FixedPoint/Brouwer.Brouwer`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FixedPoint/Brouwer.Brouwer` (`✓ std3`). ∎

*Citation.* Math_XMUM (2025). *Brouwer fixed-point theorem via Scarf's lemma*. URL: <https://github.com/math-xmum/Brouwer/tree/f9dc162170e8711f78059a87edcd38ffc44a1bfb>.

*Commentary.*

For every positive natural n and continuous self-map of the real standard simplex indexed by Fin n, there exists x with f(x)=x. This includes the singleton simplex n=1. Continuity is the only analytic map hypothesis.

Color each lattice point by a coordinate not decreased by f. Scarf supplies colorful dominant cells. Coordinate estimates force their diameters to zero and coordinates outside a constant color set to zero. Finite pigeonhole and compactness give monotone subsequences. Points of each surviving color converge to the same limit; continuity gives coordinatewise inequalities, and the unit sums force equality.

The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion.

## References

- Truth anchor: `D5/S3/Geometry/FixedPoint/Brouwer.Brouwer`
- Dependency: [D5/S3/Geometry/FixedPoint/SimplexMesh](SimplexMesh.md)
