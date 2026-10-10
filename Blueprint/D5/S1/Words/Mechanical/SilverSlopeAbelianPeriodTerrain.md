# Silver Pell arithmetic and convergent periods

## Abstract

Pell approximation estimates and convergent-period constructions for the silver slope.

**Theorem 1.1 (Every convergent denominator is a minimum period).**

$$\forall k \in \mathbb{N},\; \exists n \in \mathbb{N},\; \exists i \in \mathbb{N},\; 0 < n \land \operatorname{minAbelianPeriod}(\operatorname{lowerMechanicalFactor}(\operatorname{silverSlope}(), 0, n, i)) = \operatorname{P}(k + 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodTerrain.silver_q_realisation` (`✓ std3`). ∎

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Proposition 5.5 is realised by a long list of equal-count blocks; every smaller period contradicts the endpoint error estimate. The operators real and integer denote canonical numeric coercions.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodTerrain.silver_q_realisation`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic](SilverSlopeAbelianPellArithmetic.md)
