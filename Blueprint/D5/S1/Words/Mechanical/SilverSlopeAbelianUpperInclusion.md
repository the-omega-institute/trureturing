# Exclusion of noncandidate minimum periods

## Abstract

Exclusion of noncandidate minimum periods

**Theorem 1.1 (Packing contradicts a noncandidate decomposition).**

$$\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall i \in \mathbb{N},\; \forall m \in \mathbb{N},\; \left(1 \le k \land \left(\operatorname{P}(k + 1) \le m \land \left(m < \operatorname{P}(k + 2) \land \left(m \ne \operatorname{P}(k + 1) \land \left(m \ne 2 \cdot \operatorname{P}(k + 1) \land \left(m \ne \operatorname{P}(k + 1) + \operatorname{P}(k) \land \left(\operatorname{P}(k + 1) < n \land \neg(\operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, n, i), \operatorname{P}(k + 1)))\right)\right)\right)\right)\right)\right)\right) \Rightarrow \neg(\operatorname{AbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, n, i), m))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianUpperInclusion.silver_noncandidate_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least three the gap forces fewer than q−2 blocks, contradicting singular-window packing. The four noncandidates at k=2 have explicit rational error bounds. Canonical coercions are denoted real and integer. Natural subtraction is truncated at zero; natMod is natural remainder.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianUpperInclusion.silver_noncandidate_exclusion`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianSingularPacking](SilverSlopeAbelianSingularPacking.md)
