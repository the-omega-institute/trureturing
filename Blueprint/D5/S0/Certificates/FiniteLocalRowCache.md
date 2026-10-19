# Exact local-row transition cache soundness

## Abstract

Exact local-row transition cache soundness

A state associates an original row assignment with an actual partial event through an earned symmetry action. The generic theorem checks an entire transition assignment, transports the actual coordinate fill through the previous action, and composes the new action with the old one. It supplies no concrete table acceptance and does not substitute a producer premise for the actual row checker.

**Definition 1.1 (Whole-function row association).**

Lean statement: `D5/S0/Certificates/FiniteLocalRowCache.Associated`

*Formalization.* `D5/S0/Certificates/FiniteLocalRowCache.Associated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original stored row assignment equals the actual partial action of the earned symmetry on the complete original partial event.

**Definition 1.2 (Exact entire assignment transition check).**

Lean statement: `D5/S0/Certificates/FiniteLocalRowCache.checkTransition`

*Formalization.* `D5/S0/Certificates/FiniteLocalRowCache.checkTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The next row assignment must equal the actual next action applied to the original row assignment with this coordinate and value filled.

**Definition 1.3 (Transport the real fill before a row transition).**

Lean statement: `D5/S0/Certificates/FiniteLocalRowCache.step`

*Formalization.* `D5/S0/Certificates/FiniteLocalRowCache.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The old action determines the representative coordinate preimage and transformed value. The returned action is composed with the old earned action in the supplied proven order.

**Theorem 1.4 (A checked transition preserves the actual association).**

Lean statement: `D5/S0/Certificates/FiniteLocalRowCache.checked_step_associated`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteLocalRowCache.checked_step_associated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual update and composition laws, the old full association and the complete transition check establish the new full association after the original coordinate fill.

**Theorem 1.5 (An accepted original row bounds the original compatible event).**

Lean statement: `D5/S0/Certificates/FiniteLocalRowCache.associated_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FiniteLocalRowCache.associated_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete actual row acceptance gives a bound on the transported compatible completion. Exact score invariance returns the same bound on the original completion.

## References

- Truth anchor: `D5/S0/Certificates/FiniteLocalRowCache.Associated`
- Truth anchor: `D5/S0/Certificates/FiniteLocalRowCache.associated_lower_bound`
- Truth anchor: `D5/S0/Certificates/FiniteLocalRowCache.checkTransition`
- Truth anchor: `D5/S0/Certificates/FiniteLocalRowCache.checked_step_associated`
- Truth anchor: `D5/S0/Certificates/FiniteLocalRowCache.step`
- Dependency: [D5/S0/Certificates/FinitePartialBoundDAG](FinitePartialBoundDAG.md)
