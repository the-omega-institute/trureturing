# Finite invariant sets of transitive finitely positively expansive graph maps

## Abstract

Finite invariant sets of transitive finitely positively expansive graph maps

**Theorem 1.1 (A proper finite totally invariant set is empty).**

Lean statement: `D5/S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller.finite_totally_invariant_eq_empty`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller.finite_totally_invariant_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a nonempty finite totally invariant set exists. An iterate fixes the periodic incident arms and sends the other arms into them. Each periodic arm must move short distances away from its base point. An attracting arm would put an interval in a single forward Bowen ball. Choosing short neighborhoods along the arms gives a nonempty open set that backward iteration preserves and that misses another nonempty open set. This contradicts transitivity.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller.finite_totally_invariant_eq_empty`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteGraphBowenArcs](FiniteGraphBowenArcs.md)
