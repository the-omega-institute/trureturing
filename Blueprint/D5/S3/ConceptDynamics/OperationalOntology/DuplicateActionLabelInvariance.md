# Duplicate Action Label Invariance

## Abstract

Replicating labels for existing action behaviors does not create operational freedom.

**Definition 1.1 (The retained-label map descends to behavior classes).**

$$\begin{gathered}\forall A, Aplus, W, O: \operatorname{Type},\\{}Prof: A \to \left(W \to O\right), ProfPlus: Aplus \to \left(W \to O\right),\\{}i: A \to Aplus, r: Aplus \to A,\\{}\operatorname{LeftInverse}\left(r, i\right) \land (\forall a: Aplus, ProfPlus(a) = Prof(r(a))) \Rightarrow\\{}\operatorname{actionLabelQuotientMap}\left(Prof, ProfPlus, i, r\right): \operatorname{QuotientKer}\left(Prof\right) \to \operatorname{QuotientKer}\left(ProfPlus\right).\end{gathered}$$

*Formalization.* `D5/S3/ConceptDynamics/OperationalOntology/DuplicateActionLabelInvariance.actionLabelQuotientMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each extended label is assigned an original representative with the same complete continuation profile, while the retained original labels retract to themselves. The inclusion therefore induces the displayed map between the two profile-kernel quotients.

**Proposition 1.2 (Duplicate labels preserve effective action space and capacity).**

$$\begin{aligned}\forall A, Aplus, W, O: \operatorname{Type},\\\operatorname{Finite}\left(A\right), \operatorname{Finite}\left(Aplus\right),\\Prof: A \to \left(W \to O\right), ProfPlus: Aplus \to \left(W \to O\right),\\i: A \to Aplus, r: Aplus \to A,\\\operatorname{LeftInverse}\left(r, i\right) \land (\forall a: Aplus, ProfPlus(a) = Prof(r(a))) \Rightarrow\\\operatorname{Bijective}\left(\operatorname{actionLabelQuotientMap}\left(Prof, ProfPlus, i, r\right)\right) \land\\\operatorname{log2}\left(\operatorname{card}\left(\operatorname{QuotientKer}\left(Prof\right)\right)\right) = \operatorname{log2}\left(\operatorname{card}\left(\operatorname{QuotientKer}\left(ProfPlus\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalOntology/DuplicateActionLabelInvariance.duplicate_action_labels_preserve_effective_space` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The profile functions are source-semantic primitives: they record the outcome for every continuation. No quotient or capacity is defined to be the theorem's conclusion.

The canonical map induced by retaining old labels is bijective. Its inverse sends every extended label to its chosen behaviorally equivalent original representative; the two inverse laws hold after quotienting by complete-profile equality.

For finite label types, equivalence of the effective quotients gives equal cardinalities and hence equal base-two log-cardinality operational capacities.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalOntology/DuplicateActionLabelInvariance.actionLabelQuotientMap`
- Truth anchor: `D5/S3/ConceptDynamics/OperationalOntology/DuplicateActionLabelInvariance.duplicate_action_labels_preserve_effective_space`
