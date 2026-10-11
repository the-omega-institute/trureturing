# Native fragment preservation by the original algorithm

## Abstract

Native fragment preservation by the original algorithm.

Constraint.unifyOne, Constraints.unifyCore and Constraints.unify retain the pinned Strata algorithm, including actual returned states and termination proofs. The new native invariant follows the same mutual recursion; neither the algorithm nor its accepted syntax is redesigned.

**Theorem 1.1 (Every successful equation step).**

Lean statement: `D5/S0/Rewriting/NativeTermUnification.unifyOne_native`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeTermUnification.unifyOne_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every equation, current state, returned relation and actual success equality, native input terms and native current substitution values imply native returned substitution values. Both variable orientations, existing bindings, fresh bindings and decomposed constructor equations are included.

**Theorem 1.2 (Every successful list step).**

Lean statement: `D5/S0/Rewriting/NativeTermUnification.unifyCore_native`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeTermUnification.unifyCore_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every equation list, state and successful returned relation, native current values and native terms on both sides of every equation imply native output values.

**Theorem 1.3 (Successful native output).**

Lean statement: `D5/S0/Rewriting/NativeTermUnification.unify_native`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeTermUnification.unify_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every successful actual unify call, native equations and native current substitution values imply native output values. Free-variable bounds alone do not establish this constructor invariant.

## References

- Truth anchor: `D5/S0/Rewriting/NativeTermUnification.unifyCore_native`
- Truth anchor: `D5/S0/Rewriting/NativeTermUnification.unifyOne_native`
- Truth anchor: `D5/S0/Rewriting/NativeTermUnification.unify_native`
- Dependency: [D5/S0/Rewriting/NativeSubstitution](NativeSubstitution.md)
