# Rational rank-three completion at the boundary

## Abstract

The arithmetic of rank-three Fibonacci completions at a disk boundary.

**Theorem 1.1 (Exact boundary criterion).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibRationalBoundary.rational_rank_three_boundary_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibRationalBoundary.rational_rank_three_boundary_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For compatible rational coherent edge data at positive middle occupation, a trace-one positive semidefinite extension of rank at most three with rational entries and a boundary coupling exists exactly when the residual disk intersection contains a rational point on either circle. This holds in the following cases.

If a circle meets the strict interior of the other disk, it contributes such a point exactly when its squared radius is a sum of two rational squares. Translation and multiplication by a Gaussian rational of the prescribed norm reduce the problem to the unit circle. The Cayley parametrization supplies rational points in the required arc. A circle of radius zero contributes its center.

If the circles coincide, the common squared radius must be a sum of two rational squares. For simultaneous equalities with distinct centers p and q and squared radii r and s, put d = |q − p|² and t = (d + r − s) / (2d). The real part of (z − p) / (q − p) equals t. Both equalities are possible at a rational z exactly when r / d − t² is a rational square.

At such a point at least one Schur residual is singular. Their normalized tensor product and restoration of the positive pivot give the asserted rank and preserve rationality. Conversely every rational extension at the boundary reads out a rational coupling satisfying one of the cases.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibRationalBoundary.rational_rank_three_boundary_iff`
- Dependency: [D5/S3/Quantum/AURICOmega/OmegaShadowBridge](../../AURICOmega/OmegaShadowBridge.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibQuadraticCompletion](FibQuadraticCompletion.md)
