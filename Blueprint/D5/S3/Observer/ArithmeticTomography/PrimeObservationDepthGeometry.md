# Prime Observation Depth and Geometry

## Abstract

Prime-power depth and prime-prefix depth meet the same information lower bound, while an explicit equal-storage example separates their fault geometry.

**Lemma 1.1 (Horizontal cardinality depth is least).**

$$\forall N \in \mathbb{N}, \operatorname{IsLeast}\left(\{r \in \mathbb{N} \mid N \leq \operatorname{primePrefixProduct}\left(r\right)\}, \operatorname{horizontalCardinalityDepth}\left(N\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.horizontal_cardinality_depth_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing horizontal depth uses the inclusive interval from zero through its argument. Evaluating it at N minus one gives the least prime-prefix length whose product is at least the cardinality N.

**Theorem 1.2 (Vertical prime-power depth is least).**

$$\forall p, N \in \mathbb{N}, 1 < p \Rightarrow \operatorname{IsLeast}\left(\{k \in \mathbb{N} \mid N \leq p^{k}\}, \operatorname{verticalDepth}\left(p, N\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.vertical_depth_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a base greater than one, verticalDepth is the least natural exponent whose prime-power capacity reaches the requested window size.

**Theorem 1.3 (Vertical depth is the ceiling logarithm).**

$$\forall p, N \in \mathbb{N}, \operatorname{verticalDepth}\left(p, N\right) = \operatorname{natCeil}\left(\operatorname{logb}\left(p, N\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.vertical_depth_eq_natCeil_logb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib identifies its natural upper logarithm with the natural ceiling of the totalized real logarithm, including zero and one.

**Theorem 1.4 (Horizontal and vertical bit costs meet the capacity bound).**

$$\forall p \in \operatorname{NatPrimes}, N \in \mathbb{N},\\{}\operatorname{horizontalBitCost}\left(\operatorname{horizontalCardinalityDepth}\left(N\right)\right) = \operatorname{logb}\left(2, \operatorname{primePrefixProduct}\left(\operatorname{horizontalCardinalityDepth}\left(N\right)\right)\right) \land \operatorname{logb}\left(2, N\right) \leq \operatorname{horizontalBitCost}\left(\operatorname{horizontalCardinalityDepth}\left(N\right)\right) \land \operatorname{logb}\left(2, N\right) \leq \operatorname{verticalBitCost}\left(p, N\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.horizontal_vertical_bit_cost_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The horizontal sum is the base-two logarithm of the selected initial prime product. Its least-depth capacity bound therefore yields the horizontal information lower bound.

For N at least two, the generic finite-prime information theorem is applied to the singleton prime with precision verticalDepth. The zero- and one-state windows are checked separately.

**Proposition 1.5 (A base greater than one is necessary).**

$$\neg \operatorname{IsLeast}\left(\{k \in \mathbb{N} \mid 2 \leq 1^{k}\}, \operatorname{verticalDepth}\left(1, 2\right)\right) \land \neg (\operatorname{logb}\left(2, 2\right) \leq \operatorname{verticalBitCost}\left(1, 2\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.base_gt_one_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At base one and window size two, no exponent reaches the window and the claimed logarithmic cost is zero. This concrete counterexample certifies the only nondefinition hypothesis used by the depth law.

**Theorem 1.6 (Equal bit cost has different fault geometry).**

$$\operatorname{storedChannelBitCost}\left(verticalModuli, 1\right) = \operatorname{storedChannelBitCost}\left(horizontalModuli, 2\right) \land \operatorname{MinDistanceAtLeast}\left(horizontalModuli, 2, 6, 1\right) \land \operatorname{AgreeOutside}\left(verticalModuli, 1, 0, 0, 2\right) \land \neg \operatorname{AgreeOutside}\left(horizontalModuli, 2, 0, 0, 2\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.same_bit_cost_different_fault_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A single modulus-eight channel and separate modulus-two and modulus-three channels each require three rounded storage bits.

The prime pair has distance at least one on the six-state window. Removing the modulus-two coordinate still separates zero from two, whereas removing the sole modulus-eight coordinate hides that pair completely.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.base_gt_one_is_necessary`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.horizontal_cardinality_depth_isLeast`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.horizontal_vertical_bit_cost_lower_bounds`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.same_bit_cost_different_fault_geometry`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.vertical_depth_eq_natCeil_logb`
- Truth anchor: `D5/S3/Observer/ArithmeticTomography/PrimeObservationDepthGeometry.vertical_depth_isLeast`
- Dependency: [D5/S3/Arith/Coding/HorizontalCompletenessDepth](../../Arith/Coding/HorizontalCompletenessDepth.md)
- Dependency: [D5/S3/Arith/Coding/ResidueCodeDynamicRange](../../Arith/Coding/ResidueCodeDynamicRange.md)
- Dependency: [D5/S3/Observer/ArithmeticTomography/FinitePrimeInformationBudget](FinitePrimeInformationBudget.md)
