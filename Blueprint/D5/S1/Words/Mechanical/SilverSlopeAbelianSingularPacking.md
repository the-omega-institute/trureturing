# Singular-window separation and packing

## Abstract

Singular-window separation and packing

**Theorem 1.1 (Singular starts are separated).**

$$\forall k \in \mathbb{N},\; \forall u \in \mathbb{N},\; \forall v \in \mathbb{N},\; \left(1 \le k \land \left(u < v \land \left(\operatorname{count}(true, \operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, \operatorname{P}(k + 1), u)) \ne \operatorname{P}(k) \land \operatorname{count}(true, \operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, \operatorname{P}(k + 1), v)) \ne \operatorname{P}(k)\right)\right)\right) \Rightarrow \operatorname{P}(k + 2) \le v - u$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking.silver_singular_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two exceptional q-window counts place their phases in an interval of length alpha to the power k+1. A closer return contradicts the best approximation bound. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

**Theorem 1.2 (Failure of period q forces a long word).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall i \in \mathbb{N},\; \left(1 \le k \land \left(\operatorname{P}(k + 1) < n \land \neg(\operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, n, i), \operatorname{P}(k + 1)))\right)\right) \Rightarrow \left(\operatorname{P}(k + 1) - 1\right) \cdot \operatorname{P}(k + 2) + \operatorname{P}(k + 1) \le n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking.silver_no_q_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every residue modulo q needs a singular full window. Their separated starts give the length bound by an injection into quotient intervals. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking.silver_no_q_length`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking.silver_singular_separation`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic](SilverSlopeAbelianPellArithmetic.md)
