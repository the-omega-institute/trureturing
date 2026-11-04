# Finite-difference propagation

## Abstract

Finite-difference propagation under local codes.

**Theorem 1.1 (Finite-window codes preserve finite disagreement).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.finite_difference_code`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.finite_difference_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two source configurations disagree on a finite set, an output can disagree only when one of the finitely many coordinates in its local window disagrees. The output disagreement set is contained in a finite union of translates of the source disagreement set.

**Definition 1.2 (Iterated local code).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.codeIter`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.codeIter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

codeIter h n applies the same finite-window code n times, with the zero iterate equal to the identity.

**Theorem 1.3 (Finite disagreement survives every finite iterate).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.finite_difference_code_iterate`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.finite_difference_code_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the iterate depth reuses finite-window propagation at each step, transporting finite-difference classes through repeated local-code evolution.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.codeIter`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.finite_difference_code`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation.finite_difference_code_iterate`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity](BipermutativePreinjectivity.md)
