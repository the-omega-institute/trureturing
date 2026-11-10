# Norm and Frobenius divisor averages

## Abstract

Uniform norm fibers and cyclic element orders produce the divisor average.

**Theorem 1.1 (Average over actual norm fibers).**

Lean statement: `D5/S3/FiniteGroups/Semilinear/WeightedArithmetic.norm_average`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Semilinear/WeightedArithmetic.norm_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Native finite-field norm surjectivity and the native equivalence between a homomorphism fiber and its kernel give uniform norm-fiber cardinalities. The kernel cardinality times card(E units) is card(K units). The exact cyclic order-count theorem gives totient(m) elements of order m for every divisor m of card(E)-1.

The scalar average is thus the sum of totient(m) times card(E) to a_m over these divisors, divided by card(E)-1. All divisions in the formal statements are rational, with no intermediate natural truncation. A cyclic power-kernel bound is never substituted for an exact order count.

**Theorem 1.2 (The Frobenius gcd and totient average).**

Lean statement: `D5/S3/FiniteGroups/Semilinear/WeightedArithmetic.fixed_average`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Semilinear/WeightedArithmetic.fixed_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write r=card(F) and n=[K:F]. Artin fixed-field degree gives [K:E]=order(sigma). The tower law then gives card(E)=r to the power n/order(sigma). The finite-field Galois group is cyclic of order n, with totient(e) elements of each order e dividing n.

The proof groups by e, then applies the native divisor involution e maps to n/e. With d=n/e this produces totient(n/d) and r to the power d. In Frobenius coordinates sigma=Frobenius to the power j, this is d=gcd(n,j), including j=0 with d=n. At every d, a_m still uses the full original coordinate set.

## References

- Truth anchor: `D5/S3/FiniteGroups/Semilinear/WeightedArithmetic.fixed_average`
- Truth anchor: `D5/S3/FiniteGroups/Semilinear/WeightedArithmetic.norm_average`
- Dependency: [D5/S3/FiniteGroups/Semilinear/WeightedFixedSets](WeightedFixedSets.md)
