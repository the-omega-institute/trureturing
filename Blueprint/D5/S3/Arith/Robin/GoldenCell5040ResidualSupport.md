# The 5040 Cell and a Four-Prime Residual

## Abstract

The four-prime residual branch of the 5040 congruence cell is covered by the existing eight-prime Robin theorem.

**Theorem 1.1 (Residual support bound).**

Lean statement: `D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.modEq_2241_card_le_eight_of_residual_card_le_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.modEq_2241_card_le_eight_of_residual_card_le_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The congruence cell has fixed prime support {2,3,5,7}. If the residual has at most four distinct prime factors, the union bound gives at most eight for the whole integer.

**Theorem 1.2 (Robin on the residual branch).**

Lean statement: `D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.robin_of_modEq_2241_residual_card_le_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.robin_of_modEq_2241_residual_card_le_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing theorem for at most eight distinct prime factors proves Robin's inequality on this branch. Residuals with five or more distinct prime factors remain open.

## References

- Truth anchor: `D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.modEq_2241_card_le_eight_of_residual_card_le_four`
- Truth anchor: `D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.robin_of_modEq_2241_residual_card_le_four`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenCell5040Shape](../GoldenResource/GoldenCell5040Shape.md)
- Dependency: [D5/S3/Arith/Robin/FewDistinctPrimes](FewDistinctPrimes.md)
