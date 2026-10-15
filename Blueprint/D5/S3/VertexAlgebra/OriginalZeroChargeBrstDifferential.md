# Complete Native BRST Matrix

## Abstract

The original Q on every basis vector of the entire exceptional sector.

**Theorem 1.1 (One nonzero column).**

$$\forall i, \operatorname{Q}\left(D, H, \operatorname{basis}\left(i\right)\right) = \operatorname{exceptionalColumn}\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstDifferential.Q_sectorBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume H times gramComplex(D)=1 and gramComplex(D) times H=1. The only nonzero column is Q(Omega tensor c0 Omega)=2 Omega tensor c1 c(-1) Omega. Every other vector in the complete sector basis is killed.

For each matter axis the frequency-one excitation with c1 Omega is killed because the original matter L0 contribution is minus the {1,3} tensor and the ghost contribution is plus that same tensor. With the c0 creator also present both contributions vanish. Positive matter modes kill these charge-zero states, and the remaining negative-mode terms vanish by native c-mode support.

Here site 1 is c1, site 3 is c0, and site 5 is c(-1); the sector also includes the triple {1,3,5}. This matrix is derived after proving the complete energy fiber, not chosen as a model for it. No selected frame or nonzero charge pairing appears.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstDifferential.Q_sectorBasis`
- Dependency: [D5/S3/VertexAlgebra/OriginalZeroChargeBrstAction](OriginalZeroChargeBrstAction.md)
