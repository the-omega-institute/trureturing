# Weighted prime-power correction

## Abstract

A three-root bound for the actual prime-power correction in the weighted Robin tail.

**Theorem 1.1 (Square, cube and fifth-root responses).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedPrimePowers.powerCorrection_le_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedPrimePowers.powerCorrection_le_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j at least 1 and x greater than 1, integrate Costa Pereira's three-root bound against the nonnegative Robin weight. For each root degree r in {2, 3, 5}, the contribution is the integral of the power t^(1/r) against that weight plus J(rj, x^(1/r))/r. The three power integrals converge because 1/r is less than j.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedPrimePowers.powerCorrection_le_roots`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel](../../../Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel.md)
