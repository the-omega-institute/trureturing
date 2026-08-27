# Descriptive and Normative Structure Separation

## Abstract

One descriptive structure admits incompatible normative extensions.

**Theorem 1.1 (Descriptive structure does not uniquely determine norms).**

$$\forall State, Action, Description: \operatorname{Type},\\{}descriptive: \operatorname{DescriptiveStructure}(State, Action, Description), action: Action,\\{}\exists M_{1}, M_{2}: \operatorname{NormativeExtension}(State, Action, Description),\\{}\operatorname{Desc}(M_{1}) = descriptive \land \operatorname{Desc}(M_{2}) = descriptive \land\\{}(\forall x: State, u: Action, \operatorname{Permitted}(M_{1})(x)(u)) \land\\{}(\forall x: State, u: Action, \neg \operatorname{Permitted}(M_{2})(x)(u)) \land\\{}\operatorname{Permitted}(M_{1}) \neq \operatorname{Permitted}(M_{2}) \land\\{}\forall I: \operatorname{DescriptiveStructure}(State, Action, Description) \to \left(State \to \left(Action \to \operatorname{Prop}\right)\right), \neg (I(descriptive) = \operatorname{Permitted}(M_{1}) \land I(descriptive) = \operatorname{Permitted}(M_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/DescriptiveNormativeSeparation.descriptive_structure_does_not_uniquely_determine_norms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The descriptive record contains the state carrier, physical-admissibility predicate, state-action process, concept readout, and anchored state. A normative extension independently adds a permission predicate on state-action pairs.

The first constructed model permits every state-action pair; the second permits none. Both carry exactly the supplied descriptive record, but their permission predicates differ at the public anchor and action witness.

Consequently no single function of that shared descriptive record can equal both normative predicates. All model-separation clauses and the explicit failure of unique descriptive inference occur in the public theorem.

The source proof itself uses the all-true and all-false predicates, so the formal nontriviality is their genuine normative distinction rather than an invented requirement that each predicate be nonconstant.

Repository and pinned-library searches found no exact theorem or canonical normative-extension carrier packaging this construction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/DescriptiveNormativeSeparation.descriptive_structure_does_not_uniquely_determine_norms`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
