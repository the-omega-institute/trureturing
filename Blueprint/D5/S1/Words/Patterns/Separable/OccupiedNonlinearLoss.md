# Nonlinear loss convolution for the occupation profile

## Abstract

The actual paired loss kernel has a uniform bound on the squared logarithmic profile.

**Definition 1.1 (Paired term at positive jump size).**

$$\operatorname{lossSummand}\left(x, i\right)=\operatorname{lossWeight}\left(i\right)\cdot \operatorname{discrepancyProfile}\left(x+(i+1)\right)^{2}+\operatorname{lossWeight}\left(i\right)\cdot \operatorname{discrepancyProfile}\left(x-(i+1)\right)^{2}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.lossSummand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer origin is x. The natural index i corresponds to the positive jump i+1 in both directions. The coefficient is the actual loss weight, including its singleton correction.

**Definition 1.2 (Actual paired loss convolution).**

$$\operatorname{lossConvolution}\left(x\right)=\sum_{i=0}^{\infty} \operatorname{lossSummand}\left(x, i\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.lossConvolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The following theorem verifies that this real series is summable at every integer origin.

**Theorem 1.3 (Uniform bound, including the origin).**

$$\begin{gathered}\operatorname{Summable}\left(x\mapsto \operatorname{discrepancyProfile}\left(x\right)^{2}\right) \land (\forall x, \operatorname{Summable}\left(i\mapsto \operatorname{lossSummand}\left(x, i\right)\right)) \land\\{}\exists B\ge0, \forall x, \operatorname{lossConvolution}\left(x\right)\le B\cdot \operatorname{discrepancyProfile}\left(x\right)^{2}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.actual_loss_convolution_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The profile is taken from AbsoluteDiscrepancySeries. All occurrences of x range over the integers, and the one nonnegative constant B controls every x, including zero.

The square is summable by the decreasing integral test for the shifted inverse log-square function. When the shifted location has absolute value at least half the incoming absolute value, their squared profiles are directly comparable. Otherwise the jump size is at least half the incoming distance, so the strict coefficient remainder supplies a power bound and summability controls the shifted profile mass. At the origin the far case cannot occur.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.actual_loss_convolution_bound`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.lossConvolution`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss.lossSummand`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries](../../../../S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedComparison](OccupiedComparison.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedKernelCoefficient](OccupiedKernelCoefficient.md)
