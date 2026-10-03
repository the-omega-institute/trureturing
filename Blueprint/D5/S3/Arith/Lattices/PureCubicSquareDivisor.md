# Square Divisors in a Pure Cubic Order

## Abstract

A prime square in a cubic radicand gives an integral element outside the displayed order.

**Theorem 1.1 (An explicit element of the normalization).**

Lean statement: `D5/S3/Arith/Lattices/PureCubicSquareDivisor.square_divisor_obstructs_maximality`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/PureCubicSquareDivisor.square_divisor_obstructs_maximality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K have a rational power basis (1, theta, theta squared) of dimension three, with theta cubed equal to 1 + 9a for an integer a. The integer span of 1, theta, and beta = (1 + theta + theta squared)/3 is an integral subring.

Suppose that the square of a prime p other than three divides 1 + 9a. Then theta squared divided by p is integral: its cube is an integer. It cannot lie in the displayed subring. Indeed, comparison of theta-squared coefficients in the rational power basis would force p to divide three.

Thus the displayed subring is strictly smaller than the full ring of integers whenever such a square divisor occurs. The argument supplies an obstruction to maximality; it does not assert maximality when no such divisor occurs.

## References

- Truth anchor: `D5/S3/Arith/Lattices/PureCubicSquareDivisor.square_divisor_obstructs_maximality`
- Dependency: [D5/S3/Arith/Lattices/PureCubicSuborder](PureCubicSuborder.md)
