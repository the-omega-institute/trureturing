# A Pure Cubic Suborder

## Abstract

The integral cubic lattice is a subring with an explicit multiplication table.

**Theorem 1.1 (The integer span closes under multiplication).**

Lean statement: `D5/S3/Arith/Lattices/PureCubicSuborder.pure_cubic_suborder`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/PureCubicSuborder.pure_cubic_suborder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a characteristic-zero field with a rational power basis (1, theta, theta squared) of dimension three. Let a be an integer and assume theta cubed is 1 + 9a. Set beta to (1 + theta + theta squared)/3.

The multiplication table is theta squared = 3 beta - theta - 1, theta beta = beta + 3a, and beta squared = beta + a theta + 2a. Consequently every product of integer linear combinations of 1, theta, and beta is another such combination. Their integer span is a subring of K, and every element of it is integral over the integers. The triple (1, theta, beta) is a rational basis of K.

## References

- Truth anchor: `D5/S3/Arith/Lattices/PureCubicSuborder.pure_cubic_suborder`
- Dependency: [D5/S3/Arith/Lattices/PureCubicIntegralLattices](PureCubicIntegralLattices.md)
