# All smaller witness periods are excluded

## Abstract

All smaller witness periods are excluded

**Theorem 1.1 (The convergent period is absent).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall i \in \mathbb{N},\; \left(1 \le k \land \left(2 \cdot \operatorname{P}(k + 1) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) + \operatorname{P}(k + 1) - 1 \le n \land \left(\operatorname{Even}(k) \Rightarrow \left(i = 2 \cdot \operatorname{P}(k + 1) + \operatorname{P}(k) \lor i = \operatorname{P}(k + 1) + 1\right)\right)\right)\right) \Rightarrow \neg(\operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, n, i), \operatorname{P}(k + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_no_q_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint phase displacement and the best approximation bound exclude every possible head alignment. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

**Theorem 1.2 (The adjacent-denominator sum is absent from the twice-denominator witness).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \neg(\operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, 2 \cdot \operatorname{P}(k + 1) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) + \operatorname{P}(k + 1) - 1, 2 \cdot \operatorname{P}(k + 1) + \operatorname{P}(k)), \operatorname{P}(k + 1) + \operatorname{P}(k)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_w2_no_r_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint floor telescope excludes the adjacent-denominator sum for every possible head alignment. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

**Theorem 1.3 (The remaining shorter periods are absent).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall i \in \mathbb{N},\; \forall m \in \mathbb{N},\; \left(1 \le k \land \left(2 \cdot \operatorname{P}(k + 1) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) + \operatorname{P}(k + 1) - 1 \le n \land \left(0 < m \land \left(m < 2 \cdot \operatorname{P}(k + 1) \land \left(m \ne \operatorname{P}(k + 1) \land m \ne \operatorname{P}(k + 1) + \operatorname{P}(k)\right)\right)\right)\right)\right) \Rightarrow \neg(\operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, n, i), m))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_short_period_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Word length forces enough complete blocks that the approximation error contradicts the exponent bound. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_no_q_period`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_short_period_exclusion`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions.silver_w2_no_r_period`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic](SilverSlopeAbelianPellArithmetic.md)
