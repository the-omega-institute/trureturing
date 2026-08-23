# Vacuous Omniscience

## Abstract

Empty evidence fibers induce vacuous omniscience, while fiber witnesses prevent the collapse and robust knowledge supplies such a witness.

**Theorem 1.1 (An empty evidence fiber knows every predicate).**

$$\forall X \in Type, B \in Type, A \in X \to Prop, e \in X \to B, b \in B,\; \left(\forall x \in X,\; A\left(x\right) \Rightarrow \left(\neg e\left(x\right) = b\right)\right) \Rightarrow \left(\forall P \in X \to Prop,\; \operatorname{fiberKnowledge}\left(A, e, b, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience.empty_fiber_knows_everything` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The admissible evidence fiber over b consists of the admissible states whose evidence equals b. If this fiber is empty, there is no state at which a candidate predicate can fail the fiberwise knowledge condition.

Consequently every state predicate is fiberwise known at b. This is the vacuous-omniscience collapse caused by asking for universal agreement over an empty collection.

**Lemma 1.2 (A fiber witness excludes vacuous omniscience).**

$$\forall X \in Type, B \in Type, A \in X \to Prop, e \in X \to B, b \in B,\; \left(\exists x \in X,\; A\left(x\right) \land e\left(x\right) = b\right) \Rightarrow \left(\exists P \in X \to Prop,\; \neg \operatorname{fiberKnowledge}\left(A, e, b, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience.nonempty_fiber_excludes_vacuous_omniscience` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state in the admissible evidence fiber prevents all predicates from being known there. The constantly false predicate fails at that witness, so it provides a specific predicate whose fiberwise knowledge assertion is false.

**Lemma 1.3 (Robust knowledge supplies a fiber witness).**

$$\forall X \in Type, B \in Type, A \in X \to Prop, e \in X \to B, P \in X \to Prop, a \in X,\; \operatorname{robustKnowledge}\left(A, e, P, a\right) \Rightarrow \left(\exists x \in X,\; A\left(x\right) \land e\left(x\right) = e\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience.robust_knowledge_supplies_fiber_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Robust knowledge requires its anchor to be admissible. The anchor also has the same evidence as itself, so it lies in its own admissible evidence fiber and witnesses that the fiber is nonempty.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience.empty_fiber_knows_everything`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience.nonempty_fiber_excludes_vacuous_omniscience`
- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/VacuousOmniscience.robust_knowledge_supplies_fiber_witness`
- Dependency: [D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeFactivity](RobustKnowledgeFactivity.md)
