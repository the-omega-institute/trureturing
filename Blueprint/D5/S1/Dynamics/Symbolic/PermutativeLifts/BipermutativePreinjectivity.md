# Finite-difference preinjectivity

## Abstract

Finite-difference preinjectivity for bipermutative two-sided codes.

**Definition 1.1 (Finite-difference relation).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.FiniteDifference`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.FiniteDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two integer configurations are finitely different when their disagreement set is finite.

**Definition 1.2 (Finite-difference preinjectivity predicate).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.Preinjective`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.Preinjective` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate requires equal code outputs to force equal source configurations whenever the sources differ on only finitely many coordinates.

**Theorem 1.3 (Bipermutative codes are preinjective).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.preinjective_code`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.preinjective_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a bipermutative local rule, a finite disagreement has a greatest coordinate. The right tail of the corresponding windows agrees, so injectivity in the left endpoint forces agreement at the greatest coordinate, a contradiction.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.FiniteDifference`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.Preinjective`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity.preinjective_code`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift](BipermutativeLift.md)
