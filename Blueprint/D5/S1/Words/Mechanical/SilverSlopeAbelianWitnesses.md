# Exact minimum periods of both silver witness families

## Abstract

Exact minimum periods of both silver witness families

**Theorem 1.1 (Minimum twice a Pell denominator).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \left(0 < 2 \cdot \operatorname{P}(k + 1) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) + \operatorname{P}(k + 1) - 1 \land \operatorname{minAbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, 2 \cdot \operatorname{P}(k + 1) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) + \operatorname{P}(k + 1) - 1, 2 \cdot \operatorname{P}(k + 1) + \operatorname{P}(k))) = 2 \cdot \operatorname{P}(k + 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses.silver_w2_min_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit decomposition supplies period 2q. Every smaller period is ruled out, including q and q+t. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

**Theorem 1.2 (Minimum the adjacent-denominator sum).**

$$\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \left(0 < \left(2 \cdot \operatorname{P}(k + 1) + 1\right) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) - \operatorname{if}(\operatorname{natMod}(k, 2) = 1, 1, 2) \land \operatorname{minAbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, \left(2 \cdot \operatorname{P}(k + 1) + 1\right) \cdot \left(\operatorname{P}(k + 1) + \operatorname{P}(k)\right) - \operatorname{if}(\operatorname{natMod}(k, 2) = 1, 1, 2), \operatorname{if}(\operatorname{natMod}(k, 2) = 1, 0, \operatorname{P}(k + 1) + 1))) = \operatorname{P}(k + 1) + \operatorname{P}(k)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses.silver_wr_min_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parity-dependent decomposition supplies period q+t. Every smaller period is ruled out. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses.silver_w2_min_period`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses.silver_wr_min_period`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessExclusions](SilverSlopeAbelianWitnessExclusions.md)
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianWitnessPeriods](SilverSlopeAbelianWitnessPeriods.md)
