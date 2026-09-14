# Adaptive affine message data

## Abstract

Exact rational affine coefficients and certificate patterns for actual geometric states.

**Definition 1.1 (Actual state coefficients).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affineCoefficients`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affineCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each of the 881 increasing geometric masks has a slope and intercept with denominator one million. Repeated pairs share storage. No state quotient, transition equivalence or numerical solver verdict is assumed.

**Definition 1.2 (Clamping pattern).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affinePattern`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affinePattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three base-three digits select lower endpoint, upper endpoint or interior coordinates. Pattern 27 selects the everywhere favorable residual case. The consumer recomputes the level and checks the full rational certificate against actual geometric successors.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affineCoefficients`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affinePattern`
