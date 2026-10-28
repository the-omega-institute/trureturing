# Exact inverse Laguerre moment

## Abstract

Exact inverse Laguerre moment

These supplier proofs are reused from commit 73c64f70. The underlying polynomial and moment definitions retain their OpenAI/math attribution and Apache-2.0 license. The argument evaluates polynomial Gamma integrals and their integration-by-parts recurrence; no boundary-value or completeness premise is assumed.

**Theorem 1.1 (Every actual inverse moment is integrable).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment.centralPsi_integrable_inverse_square`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment.centralPsi_integrable_inverse_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural mode n, x^(5/2) times psi_n(x)^2 is integrable on x>0. This supplies the near-origin absolute Mellin estimate.

**Theorem 1.2 (The exact value is independent of the mode).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment.centralPsi_integral_inverse_square`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment.centralPsi_integral_inverse_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, the same integral equals 4/7. This is an unbounded mode identity, derived from actual Laguerre orthogonality, the Gamma recurrence and the specified normalization. It is used by the uniform linear absolute Mellin bound; it is not a finite numerical certificate.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment.centralPsi_integrable_inverse_square`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment.centralPsi_integral_inverse_square`
