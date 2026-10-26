# Linear absolute central Mellin control

## Abstract

Linear absolute central Mellin control

These supplier proofs are reused from commit 73c64f70, with its actual Laguerre definitions and upstream attribution. The inverse moment controls the near-origin part; the physical Jacobi multiplication recurrence controls the tail. Both controls are proved, not assumed.

**Theorem 1.1 (Absolute Mellin integrability).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound.centralPsi_integrable_absolute_mellin`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound.centralPsi_integrable_absolute_mellin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, x^(5/4) times the absolute value of the actual normalized mode is integrable on x>0. This is consumed by both the mode bound and the physical synthesis.

**Theorem 1.2 (A uniform linear bound for every mode).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound.centralPsi_absolute_mellin_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound.centralPsi_absolute_mellin_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, the absolute central Mellin integral is at most 10(n+1). Splitting at one and applying scaled square estimates yields the stated bound from the exact inverse moment and the quadratic graph moment. This controls the infinite weighted coefficient synthesis without postulating a continuous Mellin functional.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound.centralPsi_absolute_mellin_le`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMellinAbsoluteBound.centralPsi_integrable_absolute_mellin`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment](LaguerreSevenHalfInverseMoment.md)
