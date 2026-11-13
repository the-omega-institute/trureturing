# A uniform budget for proper-divisor powers

## Abstract

A uniform budget for proper-divisor powers

The estimate keeps a full additive n margin. Complementary proper divisors lie among the integers from two through n. Mathlib supplies a finite reciprocal-square estimate; no infinite numerical approximation or finite enumeration is used. Multiplication by n^(s-2) extends the result to all natural exponents s at least two.

**Theorem 1.1 (square budget).**

Lean statement: `D5/S3/Arith/Divisors/ProperDivisorPowerBudget.square_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ProperDivisorPowerBudget.square_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map d to n/d is injective on proper divisors and gives the exact complementary reciprocal-square sum. The finite telescoping upper bound supplies n squared minus n.

**Theorem 1.2 (power budget).**

Lean statement: `D5/S3/Arith/Divisors/ProperDivisorPowerBudget.power_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ProperDivisorPowerBudget.power_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each d^s is at most n^(s-2) times d squared. Since n^(s-2) is at least one, the quadratic additive margin remains at least n. The inequality is over integers and holds at n=1 too.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ProperDivisorPowerBudget.power_budget`
- Truth anchor: `D5/S3/Arith/Divisors/ProperDivisorPowerBudget.square_budget`
