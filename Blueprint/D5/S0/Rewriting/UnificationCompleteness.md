# Unrestricted finite unification completeness

## Abstract

Unrestricted finite unification completeness.

The soundness, MGU, absorption, occurs and zipped-constructor suppliers are consumed faithful Strata reuse in this same owning unit. Unrestricted completeness is proved by mutual induction over the unchanged algorithm, using one arbitrary common substitution and the actual returned head state. The solution substitution has no well-formedness, groundness or separated-variable premise.

**Theorem 1.1 (A common solution prevents single-equation failure).**

Lean statement: `D5/S0/Rewriting/UnificationCompleteness.unifyOne_complete`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UnificationCompleteness.unifyOne_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every equation c, well-formed current state S, and arbitrary finite substitution R, if R solves c and absorbs S, the actual Constraint.unifyOne call returns a successful relation. There is no well-formedness, groundness or disjoint-variable condition on R.

**Theorem 1.2 (Completeness through the returned states).**

Lean statement: `D5/S0/Rewriting/UnificationCompleteness.unifyCore_complete`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UnificationCompleteness.unifyCore_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite equation list, current state and common substitution solving every equation and absorbing the current state, Constraints.unifyCore succeeds. The tail receives the substitution returned from the head, and the original MGU absorption law carries the same common substitution to that state.

**Theorem 1.3 (Unrestricted failure completeness).**

Lean statement: `D5/S0/Rewriting/UnificationCompleteness.unify_complete`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/UnificationCompleteness.unify_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary equations C, current SubstInfo S and Subst R, solving all of C and absorbing S implies existence of an output T with Constraints.unify C S = ok T. The occurs-check obstruction is valid for arbitrary R; constructor equality supplies every zipped argument equation.

## References

- Truth anchor: `D5/S0/Rewriting/UnificationCompleteness.unifyCore_complete`
- Truth anchor: `D5/S0/Rewriting/UnificationCompleteness.unifyOne_complete`
- Truth anchor: `D5/S0/Rewriting/UnificationCompleteness.unify_complete`
- Dependency: [D5/S0/Rewriting/NativeTermUnification](NativeTermUnification.md)
