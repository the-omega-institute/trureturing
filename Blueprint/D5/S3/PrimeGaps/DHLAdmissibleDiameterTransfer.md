# Independent occupancy and window inputs

## Abstract

Independent occupancy and window inputs.

**Theorem 1.1 (Independent occupancy and window inputs).**

$$\forall k,B\in Nat,\operatorname{DHLTwoNat}\left(k\right)\land \operatorname{AdmissibleWindowWitness}\left(k, B\right)\Rightarrow\operatorname{ArbitrarilyLateConsecutiveGap}\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeGaps/DHLAdmissibleDiameterTransfer.dhl_two_and_admissible_window_yield_bounded_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This inherited API theorem combines the exact DHLTwoNat k premise with the existence of a k-element admissible natural set whose offsets are bounded by B. It asserts arbitrarily late consecutive prime gaps in a containing window of width B; it does not prove the analytic premise.

## References

- Truth anchor: `D5/S3/PrimeGaps/DHLAdmissibleDiameterTransfer.dhl_two_and_admissible_window_yield_bounded_gap`
- Dependency: [D5/S3/PrimeGaps/ShortGapOccupancyBridge](ShortGapOccupancyBridge.md)
