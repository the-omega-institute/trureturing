# Right-permutative finite-difference preinjectivity

## Abstract

Finite-difference preinjectivity from a single endpoint permutation.

**Definition 1.1 (Right-permutative local rule).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity.RightPermutative`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity.RightPermutative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local rule is right-permutative when, after fixing the left-hand prefix, its output is injective in the right endpoint.

**Theorem 1.2 (Right-permutative codes are preinjective).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity.right_preinjective_code`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity.right_preinjective_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite disagreement set has a least integer coordinate. The windows ending there agree in their left prefix, so right-endpoint injectivity forces agreement at that least coordinate, a contradiction.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity.RightPermutative`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/RightPermutativePreinjectivity.right_preinjective_code`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/LeftPermutativePreinjectivity](LeftPermutativePreinjectivity.md)
