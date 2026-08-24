# Necessary Nonemptiness Witnesses

## Abstract

Empty types witness both nonemptiness hypotheses required by the imported theorems.

**Theorem 1.1 (An empty value type blocks factorization).**

$$\operatorname{FiberConstantButNotFactorizable}\left(emptyMarginals, emptyCouplingValue\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/NecessaryNonemptinessWitnesses.nonempty_value_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set the coupling type to Empty, the observable data type to Unit, and the target value type to Empty. Constancy on every fiber holds vacuously because there are no couplings.

A factorization would nevertheless include a function from Unit to Empty. Applying that function to the unique unit value produces an impossible element, so target nonemptiness is necessary.

**Theorem 1.2 (An empty state type blocks window sufficiency).**

$$\neg EmptyStateFiniteWindowMinimalSufficiency.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/NecessaryNonemptinessWitnesses.nonempty_state_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set the state type to Empty and the observation type to Unit at horizon zero. The window carrier Fin(1) to Unit is inhabited, while the canonical target image has no member.

The required refinement would map every zero-window value into that empty target image. Applying its factor to the constant unit window exposes an impossible state witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/NecessaryNonemptinessWitnesses.nonempty_state_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/NecessaryNonemptinessWitnesses.nonempty_value_is_necessary`
- Dependency: [D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion](../Interventions/CounterfactualIdentifiabilityCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency](FiniteWindowMinimalSufficiency.md)
