# Dynamic Closure Minimality

## Abstract

Finite intervention traces form the least intervention-closed refinement of a concept.

**Lemma 1.1 (The original concept factors through its dynamic closure).**

$$\forall X \in \operatorname{Type}, A \in \operatorname{Type}, U \in \operatorname{Type}, concept \in X \to A, intervene \in U \to \left(X \to X\right),\; \operatorname{Refines}\left(concept, \operatorname{DynClosure}\left(concept, intervene\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.concept_refines_dynamic_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dynamic closure records the concept value reached after every finite intervention word. Its coordinate at the empty word is exactly the original concept readout.

Projecting a complete trace to that empty-word coordinate therefore recovers the original concept, so the trace readout refines it.

**Lemma 1.2 (Every intervention preserves dynamic-closure fibers).**

$$\forall X \in \operatorname{Type}, A \in \operatorname{Type}, U \in \operatorname{Type}, concept \in X \to A, intervene \in U \to \left(X \to X\right),\; \operatorname{InterventionClosed}\left(\operatorname{DynClosure}\left(concept, intervene\right), intervene\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.dynamic_closure_is_intervention_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two states lie in the same dynamic-closure fiber when every finite intervention word produces the same concept value from them.

Applying one intervention merely prefixes that intervention to each word being observed. Equality of all trace coordinates is therefore preserved, making every dynamic-closure fiber intervention-invariant.

**Lemma 1.3 (Closed concept fibers persist along finite intervention words).**

$$\forall X \in \operatorname{Type}, B \in \operatorname{Type}, U \in \operatorname{Type}, candidate \in X \to B, intervene \in U \to \left(X \to X\right),\; \operatorname{InterventionClosed}\left(candidate, intervene\right) \Rightarrow \left(\forall word \in \operatorname{List}\left(U\right), x \in X, y \in X,\; candidate\left(x\right) = candidate\left(y\right) \Rightarrow candidate\left(\operatorname{runWord}\left(intervene, word, x\right)\right) = candidate\left(\operatorname{runWord}\left(intervene, word, y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.runWord_preserves_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every individual intervention preserves the fibers of a candidate concept, then every finite composition of interventions preserves those fibers as well.

The empty word changes no state. Extending a word by one intervention first uses closure for that step and then preserves equality through the remaining word, yielding the finite-word invariance.

**Theorem 1.4 (Dynamic closure is the least intervention-closed refinement).**

$$\forall X \in \operatorname{Type}, A \in \operatorname{Type}, U \in \operatorname{Type}, B \in \operatorname{Type}, concept \in X \to A, intervene \in U \to \left(X \to X\right), candidate \in X \to B,\; \left(\operatorname{Refines}\left(concept, candidate\right) \land \operatorname{InterventionClosed}\left(candidate, intervene\right)\right) \Rightarrow \operatorname{Refines}\left(\operatorname{DynClosure}\left(concept, intervene\right), candidate\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.dynamic_closure_is_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a candidate concept refine the original readout and have fibers preserved by every intervention. Finite-word invariance then shows that each complete intervention trace depends only on the candidate concept value.

Consequently the dynamic-closure readout factors through every such candidate. Together with recovery of the original readout and the closure of its own fibers, this makes dynamic closure the least intervention-closed refinement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.concept_refines_dynamic_closure`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.dynamic_closure_is_intervention_closed`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.dynamic_closure_is_least`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.runWord_preserves_fiber`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../../ObserverMemory/Prediction/ControlledBehaviorUniversality.md)
