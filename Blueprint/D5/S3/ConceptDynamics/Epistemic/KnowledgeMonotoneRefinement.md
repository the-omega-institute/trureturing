# Knowledge Monotonicity Under Nonempty Refinement

## Abstract

A nonempty refinement of a singleton-answer information state preserves the same target value.

**Theorem 1.1 (Knowledge preserves its target value under nonempty refinement).**

$$\begin{gathered}\forall X, Y: \operatorname{Type},\\{}T: X \to Y, S, S': \operatorname{Set}(X),\\{}S' \subseteq S \land S' \neq \emptyset \land (S \neq \emptyset \land \lvert \{T(x) \mid x\in S\} \rvert = 1)\\{}\Rightarrow \exists y: Y, \{T(x) \mid x\in S\} = \{y\} \land \{T(x) \mid x\in S'\} = \{y\}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/KnowledgeMonotoneRefinement.knowledge_monotone_under_nonempty_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a target readout T, the answer set of an information state S is constructed directly as the image of S under T. Knowledge at S requires S to be nonempty and this answer set to have cardinality one.

The refined state S' is publicly required to be a nonempty subset of S. The conclusion exposes one value y and states that both answer sets are exactly the singleton containing y, so the retained value is literally the same object.

Pinned Mathlib's Set.ncard_eq_one extracts y from the source knowledge test, and Set.image_mono transports the subset relation. A witness in S' supplies the reverse singleton inclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/KnowledgeMonotoneRefinement.knowledge_monotone_under_nonempty_refinement`
