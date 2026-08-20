# Binary Simplest Tail

## Abstract

One third is the binary tower's constant arm, and the golden tail is the rational tower's counterpart.

One third keeps the same normalised distance from the binary grid at every window, which is what makes its expansion the simplest periodic tail there. The arm stays fixed for an arithmetic reason: three and two are coprime, so the numerator of the distance never vanishes and the champion cannot drift toward a grid point.

The all-ones continued-fraction tail of the golden ratio is the rational tower's counterpart of the same phenomenon. Both statements already existed; neither is restated here.

The remark's remaining sentence — that a random point's normalised distance is near-uniform on the lower half interval, with liminf almost surely zero — is a numerical experiment, marked as machine-checked in the source rather than proved. It is deliberately absent from the conjunction, following the six covered atoms in the repository that carry such annotations and are covered by their provable part only.

**Theorem 1.1 (One third is the binary constant arm).**

$$\forall Q \in N,\; 1 \le Q \Rightarrow 2^{Q} \cdot \operatorname{radixDistance}\left(2, Q, \frac{1}{3}\right) = \frac{1}{3}$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/BinarySimplestTail.binary_simplest_tail_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed conjunct is the constant arm; the others are the golden tail and the exact distance formula behind the constancy. An earlier draft carried coprimality alone in that third slot, which decides trivially and mentions no window — a quantified constant rather than content.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/BinarySimplestTail.binary_simplest_tail_package`
- Dependency: [D5/S0/Tower/ConstantArms](../../../S0/Tower/ConstantArms.md)
- Dependency: [D5/S0/Tower/MetricGeometry/RadixGridDistance](../../../S0/Tower/MetricGeometry/RadixGridDistance.md)
- Dependency: [D5/S1/Depth/GoldenContinuedFraction](../GoldenContinuedFraction.md)
