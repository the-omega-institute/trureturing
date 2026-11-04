# Uniform recurrence and minimality

## Abstract

Uniform recurrence and minimality.

**Definition 1.1 (Construction).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.factorialWindow`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.factorialWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual finite interval meets at most two sufficiently long blocks. Every such adjacent block pair occurs in every block two levels higher. A following high-level boundary therefore supplies the same interval in every point, with a uniform bound of twice the larger high-level block length. Every finite coordinate pattern is reached by every integer shift orbit, proving ordinary topological minimality.

**Theorem 1.2 (Result).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.factorial_orbit_dense`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.factorial_orbit_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual finite interval meets at most two sufficiently long blocks. Every such adjacent block pair occurs in every block two levels higher. A following high-level boundary therefore supplies the same interval in every point, with a uniform bound of twice the larger high-level block length. Every finite coordinate pattern is reached by every integer shift orbit, proving ordinary topological minimality.

**Theorem 1.3 (An actual marked block occurs).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.marked_block_occurs`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.marked_block_occurs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any binary word family and actual marked tiling, a marked boundary reads exactly its current word at the same physical integer origin. This existing generic helper is public for reuse by the balanced construction; its proof is unchanged.

**Theorem 1.4 (An infix inherits an actual occurrence).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.occurs_of_infix`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.occurs_of_infix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a word is an infix of another word that occurs at integer t, it occurs at t+k for a natural prefix length k with k plus its length bounded by the enclosing word length. The publicized existing helper retains the literal coordinate origin and its original proof.

**Theorem 1.5 (Coordinate equality gives an infix).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.infix_of_coordinates`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.infix_of_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite word is an infix at natural offset p when it fits in the enclosing list and every indexed letter agrees there. The existing proof identifies it with a take of a drop and is unchanged by publicization. The balanced minimality proof consumes this helper.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.factorialWindow`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.factorial_orbit_dense`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.infix_of_coordinates`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.marked_block_occurs`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal.occurs_of_infix`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift](FactorialSubshift.md)
