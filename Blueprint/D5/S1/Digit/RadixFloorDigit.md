# Radix Floor Digits

## Abstract

Successive floors define an exact bounded radix digit.

**Theorem 1.1 (The floor carry is a bounded radix digit).**

$$0 \leq d_{b}(x) < b \land floor(bx) = bfloor(x) + d_{b}(x).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/RadixFloorDigit.radix_floor_digit_bounds_and_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The remainder floor(b x) minus b floor(x) lies between zero and b minus one and gives the exact radix decomposition.

## References

- Truth anchor: `D5/S1/Digit/RadixFloorDigit.radix_floor_digit_bounds_and_decomposition`
