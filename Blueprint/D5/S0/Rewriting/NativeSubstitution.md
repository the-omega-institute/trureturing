# Native substitution closure

## Abstract

Native substitution closure.

The original scoped substitution, its well-formedness, key-exclusion and idempotence proofs are licensed Strata reuse. Native closure is proved for the exact Boolean-leaf and binary-pair grammar by induction under these operations, independently of variable support.

**Definition 1.1 (Native substitution values).**

Lean statement: `D5/S0/Rewriting/NativeSubstitution.NativeSubst`

*Formalization.* `D5/S0/Rewriting/NativeSubstitution.NativeSubst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every stored substitution value has the exact native constructor shape; this concerns all stored values, independently of the key and free-variable bounds.

**Theorem 1.2 (Substitution closure).**

Lean statement: `D5/S0/Rewriting/NativeSubstitution.shape_subst`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeSubstitution.shape_subst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying a substitution with native values to a native term preserves the native constructor shape.

**Theorem 1.3 (Insertion closure).**

Lean statement: `D5/S0/Rewriting/NativeSubstitution.native_insert`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeSubstitution.native_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inserting one native value into a substitution with native values preserves that invariant.

**Theorem 1.4 (Composition closure).**

Lean statement: `D5/S0/Rewriting/NativeSubstitution.native_apply`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeSubstitution.native_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping a native singleton substitution through all stored values preserves the native constructor shape.

**Theorem 1.5 (Constructor decomposition).**

Lean statement: `D5/S0/Rewriting/NativeSubstitution.shape_children`

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NativeSubstitution.shape_children` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every argument of a native constructor tree is native. This supplies both sides of each decomposed equation.

## References

- Truth anchor: `D5/S0/Rewriting/NativeSubstitution.NativeSubst`
- Truth anchor: `D5/S0/Rewriting/NativeSubstitution.native_apply`
- Truth anchor: `D5/S0/Rewriting/NativeSubstitution.native_insert`
- Truth anchor: `D5/S0/Rewriting/NativeSubstitution.shape_children`
- Truth anchor: `D5/S0/Rewriting/NativeSubstitution.shape_subst`
- Dependency: [D5/S0/Rewriting/NativeUnificationCore](NativeUnificationCore.md)
