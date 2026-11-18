# Sharp moving prime-weight upper estimate

## Abstract

The moving prime remainder has a sharp upper coefficient at square-root logarithmic sharpness.

**Definition 1.1 (Explicit moving-weight majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The majorant retains the sharp central kernel correction, the central prime-density error and both geometric tails. Each term is explicit in the real cutoff P and sharpness s.

**Theorem 1.2 (Uniform finite remainder bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.remainder_le_majorant`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.remainder_le_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sufficiently large P, every s>=pi with s>=2, and every real endpoint x, remainder(P,s,x)<=majorant(P,s). The bound is uniform in x because the omitted prime terms are nonnegative.

**Theorem 1.3 (Sharp normalized majorant).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed c>0, majorant(P,c*sqrt(log(P))) divided by P/(log(P)*sqrt(log(P))) tends to pi^2/(6c) as P tends to positive infinity.

**Theorem 1.4 (Moving prime-weight upper coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.moving_weight_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.moving_weight_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed c>0 and epsilon>0, all sufficiently large P satisfy, simultaneously for every real x, remainder(P,c*sqrt(log(P)),x)<=(pi^2/(6c)+epsilon)*P/(log(P)*sqrt(log(P))). This stage proves the sharp upper coefficient used in the counting estimate. Neither an asymptotic equality for this finite remainder nor a matching lower counting bound is asserted.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.moving_weight_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.remainder_le_majorant`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/CentralWeight](CentralWeight.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/ContinuumWeight](ContinuumWeight.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit](KernelLimit.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail](Tail.md)
