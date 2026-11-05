# Original Four-M Coefficients

## Abstract

The global original inverse and its genuinely finite three-M channels.

**Theorem 1.1 (The same original inverse on each homogeneous grade).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.originalI_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.originalI_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global originalI applies the existing sourceGradePairingEquiv inverses to the actual finite graded support of normalizedCoefficient. On homogeneous inputs it is exactly the inverse used by OriginalFourMContraction, with no change of normalization or carrier. originalI_truncation preserves the existing all-state upper bound; the sharper homogeneous bound is also proved.

**Theorem 1.2 (Three statewise finite original channels).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All original M states and all integer m,n,r have statewise finite j families. For homogeneous inputs the exact ranges are j below (H+K-r).toNat, (K+L-n).toNat, and (H+L-m).toNat. The right phases remain (-1)^j and (-1)^(j+r). No infinite sum of endomorphisms is used.

**Theorem 1.3 (The exact below-two branch).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_below_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_below_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At common output weight N=H+K+L-m-n-r-2 below 2, the original fixed-parity mode and original right coefficients vanish by the existing exact cutoff facts. Thus the original homogeneous Jacobi equation is automatic in this branch; the physical ground shift is not substituted for the negative-parity module.

**Theorem 1.4 (Unrestricted detector scalarization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_scalar_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_scalar_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original homogeneous input and every signed integer triple, the full vector law is equivalent to the actualForm tests in the first pairing slot over every ActualTensor detector. The common ell cutoff is (N-1).toNat. Both integer right-transport phases and factorials remain exact. The N below 2 branch is derived, so there is no permanent N-at-least-2 premise.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.originalI_homogeneous`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_below_two`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients.original_jacobi_scalar_finite`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry](ActualPairingSymmetry.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMContraction](OriginalFourMContraction.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalRightSkew](OriginalRightSkew.md)
