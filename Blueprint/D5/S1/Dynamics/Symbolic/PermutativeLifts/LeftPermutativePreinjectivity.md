# Left-permutative finite-difference preinjectivity

## Abstract

Finite-difference preinjectivity from a single endpoint permutation.

**Definition 1.1 (Left-permutative local rule).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity.LeftPermutative`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity.LeftPermutative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local rule is left-permutative when, after fixing the right-hand tail, its output is injective in the left endpoint.

**Theorem 1.2 (Left-permutative codes are preinjective).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity.left_preinjective_code`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity.left_preinjective_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite disagreement set has a greatest integer coordinate. The windows to its right agree, so left-endpoint injectivity forces agreement at that greatest coordinate, a contradiction.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity.LeftPermutative`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity.left_preinjective_code`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity](BipermutativePreinjectivity.md)
