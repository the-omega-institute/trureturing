# The two silver witness decompositions

## Abstract

The two silver witness decompositions

**Theorem 1.1 (Twice a Pell denominator).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, 2 \cdot \operatorname{P}(k + 1) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) + \operatorname{P}(k + 1) - 1, 2 \cdot \operatorname{P}(k + 1) + \operatorname{P}(k)), 2 \cdot \operatorname{P}(k + 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods.silver_w2_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The head has length q, followed by q+t−1 blocks of length 2q and a tail of length 2q−1. Pell phase identities give the required counts. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

**Theorem 1.2 (The adjacent-denominator sum).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, \left(2 \cdot \operatorname{P}(k + 1) + 1\right) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) - \operatorname{if}(\operatorname{natMod}(k, 2) = 1, 1, 2), \operatorname{if}(\operatorname{natMod}(k, 2) = 1, 0, \operatorname{P}(k + 1) + 1)), \operatorname{P}(k + 1) + \operatorname{P}(k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods.silver_wr_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At odd index the head is empty. At even index both ends have length q+t−1. The intervening blocks have true count q−t. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods.silver_w2_period`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods.silver_wr_period`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic](SilverSlopeAbelianPellArithmetic.md)
