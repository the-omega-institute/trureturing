# Actual synthesis and central Mellin charge

## Abstract

Actual synthesis and central Mellin charge

The second physical coordinate of the weighted Laguerre synthesis belongs to L1 on x>0 with measure x^(5/4) dx. Its Bochner integral is a continuous linear functional J. This is the central Mellin charge used by the actual Gaussian coefficient core; it is not an identification with the original H6 full-line constraint.

**Theorem 1.1 (Physical integration equals actual coefficient charge).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfSynthesisCharge.synthesis_mellin_charge`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfSynthesisCharge.synthesis_mellin_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every weighted square-summable coefficient vector w, J(synthesis(w)) equals m0 times the continuous actual coefficient charge, where m0 is the positive zeroth normalized central Mellin integral. Each finite single mode is integrated against the literal measure, and continuity transports the convergent synthesis series. The actual ell2 inner-product series has the same terms; uniqueness of their sums proves the identity. No termwise integral interchange, Laguerre completeness, closed image or original-domain surjectivity is assumed. The inherited Laguerre polynomial source retains its upstream OpenAI/math attribution and Apache-2.0 notice. This source-relative result makes no RH-resolution or literature-priority claim.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfSynthesisCharge.synthesis_mellin_charge`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfWeightedSynthesis](LaguerreSevenHalfWeightedSynthesis.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianCoefficientCore](ReflectedGaussianCoefficientCore.md)
