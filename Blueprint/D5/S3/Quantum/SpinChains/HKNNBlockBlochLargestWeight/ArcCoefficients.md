# The strict coefficient deficit outside cyclic arcs

## Abstract

The strict coefficient deficit outside cyclic arcs

**Theorem 1.1 (strict_coefficient_non_arc).**

$$\forall m \in \mathbb{N},\; (1 \le m) \Rightarrow (\forall x \in \operatorname{Stationing}\left(2 \cdot m\right),\; (\neg (\operatorname{isArc}\left(m, x\right))) \Rightarrow (\lvert \operatorname{psi}\left(m, x\right)\rvert < \operatorname{castInt}\left(\operatorname{K}\left(m\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/ArcCoefficients.strict_coefficient_non_arc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A balanced cyclic binary word outside the block orbit contains alternating down-up-down-up sites or the complementary pattern. The prescribed partner swap supplies opposite signs. Unbalanced configurations have zero coefficient, and K is positive.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/ArcCoefficients.strict_coefficient_non_arc`
- Dependency: [D5/S1/Phase/SeatTowerCombinatorics](../../../../S1/Phase/SeatTowerCombinatorics.md)
- Dependency: [D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients](PairingCoefficients.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../../Zeros/Convolution/PerfectMatchingCount.md)
