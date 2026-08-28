# Algebra Descent Equivalence

## Abstract

Descent is equivalent to closure of the pullback algebra and effective-image observables.

**Theorem 1.1 (Descent and observable closure are equivalent).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}q: X \to B, F: X \to X,\\{}\operatorname{ListTFAE}\left({[\operatorname{EffectiveDescent}\left(q, F\right), \operatorname{PullbackInvariant}\left(q, F\right), \operatorname{ObservableInvariant}\left(\operatorname{realizedReadout}\left(q\right), F\right)]}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/AlgebraDescentEquivalence.descent_algebra_closure_tfae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state update descends to the canonical effective image of q exactly when the pullback algebra of q is closed under the update.

The third clause makes the dual statement explicit: every observable on the effective image, when pulled back to states, has a next-step value that is again a function of the current effective readout.

The effective-image carrier is the canonical subtype-valued realizedReadout, so the observable clause exposes the same interface object as the descent clause.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/AlgebraDescentEquivalence.descent_algebra_closure_tfae`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](DeterministicInterfaceEquivalence.md)
- Dependency: [D5/S3/ConceptDynamics/Factor/FactorInvariantObservables](../Factor/FactorInvariantObservables.md)
