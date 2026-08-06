# Ramification at Five

## Abstract

The rational prime five is the square of its ramifying golden integer.

**Theorem 1.1 (Five is a ramified square).**

$$5 = (-1+2\varphi)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenPrimeSplitting.golden_five_eq_ramified_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the golden integer ring, five equals the square of -1 + 2 phi. This is the exact ramified-square identity; it asserts neither a choice of associates nor an additional factorization convention.

## References

- Truth anchor: `D5/S3/Arith/GoldenPrimeSplitting.golden_five_eq_ramified_square`
- Dependency: [D5/S0/Carrier/Units](../../S0/Carrier/Units.md)
