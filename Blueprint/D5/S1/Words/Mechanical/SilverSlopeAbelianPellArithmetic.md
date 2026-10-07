# Silver Pell arithmetic and convergent periods

## Abstract

Pell approximation estimates and convergent-period constructions for the silver slope.

**Theorem 1.1 (The signed Pell error).**

$$\forall k \in \mathbb{N},\; \operatorname{real}(\operatorname{P}(k + 1)) \cdot \operatorname{silverSlope}() - \operatorname{real}(\operatorname{P}(k)) = \left(-1\right)^{k} \cdot \operatorname{silverSlope}()^{k + 1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silverPell_error_formula` (`✓ std3`). ∎

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

The error alternates in sign and its magnitude is the next power of the slope. The operators real and integer denote canonical numeric coercions.

**Theorem 1.2 (The adjacent Pell determinant).**

$$\forall k \in \mathbb{N},\; \operatorname{integer}(\operatorname{P}(k + 1 + 1)) \cdot \operatorname{integer}(\operatorname{P}(k)) - \operatorname{integer}(\operatorname{P}(k + 1))^{2} = \left(-1\right)^{k + 1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silverPell_determinant` (`✓ std3`). ∎

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Consecutive denominators and numerators form a unimodular pair. The operators real and integer denote canonical numeric coercions.

**Theorem 1.3 (Smaller denominators have larger error).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall z \in \mathbb{Z},\; \left(0 < m \land m < \operatorname{P}(k + 1 + 1)\right) \Rightarrow \operatorname{silverSlope}()^{k + 1} \le \left|\operatorname{real}(m) \cdot \operatorname{silverSlope}() - \operatorname{real}(z)\right|$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silver_best_approximation` (`✓ std3`). ∎

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Every positive denominator below q at index k+1 has error at least alpha to the power k+1. The operators real and integer denote canonical numeric coercions.

**Theorem 1.4 (The noncandidate approximation gap).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall z \in \mathbb{Z},\; \left(\operatorname{P}(k + 1 + 1) \le m \land \left(m < \operatorname{P}(k + 2 + 1) \land \left(m \ne \operatorname{P}(k + 1 + 1) \land \left(m \ne 2 \cdot \operatorname{P}(k + 1 + 1) \land m \ne \operatorname{P}(k + 1 + 1) + \operatorname{P}(k + 1)\right)\right)\right)\right) \Rightarrow \operatorname{silverSlope}()^{k + 2} + \operatorname{silverSlope}()^{k + 1} \le \left|\operatorname{real}(m) \cdot \operatorname{silverSlope}() - \operatorname{real}(z)\right|$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silver_gap_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Between successive Pell denominators, the three distinguished candidates are the only exceptions to the larger error bound. The operators real and integer denote canonical numeric coercions.

**Theorem 1.5 (The exact phase mass).**

$$\forall k \in \mathbb{N},\; \left(\operatorname{real}(\operatorname{P}(k + 1 + 1)) + \operatorname{silverSlope}() \cdot \operatorname{real}(\operatorname{P}(k + 1))\right) \cdot \operatorname{silverSlope}()^{k + 1} = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silver_phase_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Pell recurrence and alpha squared plus twice alpha equals one give a constant phase mass. The operators real and integer denote canonical numeric coercions.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silverPell_determinant`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silverPell_error_formula`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silver_best_approximation`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silver_gap_approximation`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic.silver_phase_mass`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs](SilverSlopeAbelianPeriodDefs.md)
- Dependency: [D5/S1/Words/Mechanical/UnimodularApproximationBound](UnimodularApproximationBound.md)
