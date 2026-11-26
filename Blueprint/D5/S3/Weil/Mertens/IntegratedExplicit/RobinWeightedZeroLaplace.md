# Weighted Laplace resolvents for zeta zeros

## Abstract

Weighted Laplace resolvents for zeta zeros.

The positive Laplace mixture represents the inverse-log weight and exchanges the two absolutely integrable variables. Each occurrence uses its actual coefficient and zero from the integrated explicit formula.

**Theorem 1.1 (One-mode resolvent).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.modeTail_resolvent`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.modeTail_resolvent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real j at least 1, every complex mode with real part below 1 and every positive lower endpoint, the weighted tail is the integral of its resolvent kernel.

**Theorem 1.2 (Derivative integral).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.weightedZeroContribution_eq_integral_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.weightedZeroContribution_eq_integral_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contribution is the weighted integral of the derivative of the integrated mode.

**Theorem 1.3 (Weighted resolvent mixture).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.weightedZeroContribution_eq_mixture`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.weightedZeroContribution_eq_mixture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed zero contribution factors into its coefficient, its exponential at the lower endpoint and the resolvent mixture.

**Theorem 1.4 (Occurrence summability).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroContribution_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroContribution_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted series indexed by all actual occurrences converges absolutely without a line hypothesis.

**Theorem 1.5 (Unconditional spectral bound).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroSum_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroSum_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm of the sum is bounded by the sum of the occurrencewise exponential majorants.

**Theorem 1.6 (First Li mass bound).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroSum_norm_le_of_line`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroSum_norm_le_of_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every actual occurrence lies on the critical line, the coefficient norms sum to the exact first Li mass.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroContribution_summable`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroSum_norm_le`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.actualWeightedZeroSum_norm_le_of_line`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.modeTail_resolvent`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.weightedZeroContribution_eq_integral_deriv`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace.weightedZeroContribution_eq_mixture`
- Dependency: [D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments](../../../Analytic/ExponentialSum/TwoScaleEndpointMoments.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula](WholeFormula.md)
