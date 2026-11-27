# Logarithmic correction for the weighted Robin tail

## Abstract

Exact power main term and logarithmic correction for the Robin weight.

**Theorem 1.1 (Exact main term with the inverse-logarithm correction).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.power_main_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.power_main_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r less than j and u positive, split H(j,v) into j/(j-r) times H(j-r,v) and the correction -r/((j-r)v²). The exponential times the first weight integrates exactly to exp((r-j)u)/u before multiplication by j/(j-r). The remaining integral retains the v⁻² factor.

**Theorem 1.2 (Two bounds for the inverse-logarithm correction).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.exponential_inverse_square_tail_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.exponential_inverse_square_tail_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and u, the integral of exp(-av)/v² over v greater than u lies between exp(-au)/(a(u+1/a)²) and exp(-au)/(au²). The upper bound uses v at least u. For the lower bound, the affine tangent to v⁻² at u+1/a has the same exponential integral as its constant term because the centered first moment vanishes.

**Theorem 1.3 (Bounds for the square-root main term).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.square_root_power_main_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.square_root_power_main_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At j = 1 and power 1/2, both bounds subtract a positive correction from 2 exp(-u/2)/u. The upper bound subtracts 2 exp(-u/2)/(u+2)², which improves the finite range estimate for the prime-power correction.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.exponential_inverse_square_tail_bounds`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.power_main_eq`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.square_root_power_main_bounds`
- Dependency: [D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments](../../../Analytic/ExponentialSum/TwoScaleEndpointMoments.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedZeroLaplace](RobinWeightedZeroLaplace.md)
