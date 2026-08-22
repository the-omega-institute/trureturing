# Complete Inputs Exclude Deterministic Disagreement

## Abstract

Deterministic disagreement exposes a difference in at least one complete input.

**Theorem 1.1 (Complete input agreement excludes deterministic disagreement).**

$$I_{l} = (C_{l}, b_{l}, A_{l}, \beta_{l}, V_{l}, U_{l}, s_{l}, x_{l}),\\{}I_{r} = (C_{r}, b_{r}, A_{r}, \beta_{r}, V_{r}, U_{r}, s_{r}, x_{r}),\\{}\forall I, u, v, (D(I, u) \land D(I, v)) \Rightarrow u = v,\\{}D(I_{l}, u_{l}) \land D(I_{r}, u_{r})\\{}\Rightarrow [((C_{l} = C_{r} \land b_{l} = b_{r} \land A_{l} = A_{r} \land \beta_{l} = \beta_{r} \land V_{l} = V_{r} \land U_{l} = U_{r} \land s_{l} = s_{r} \land x_{l} = x_{r}) \Rightarrow u_{l} = u_{r})\\{}\land (u_{l} \neq u_{r} \Rightarrow C_{l} \neq C_{r} \lor b_{l} \neq b_{r} \lor A_{l} \neq A_{r} \lor \beta_{l} \neq \beta_{r} \lor V_{l} \neq V_{r} \lor U_{l} \neq U_{r} \lor s_{l} \neq s_{r} \lor x_{l} \neq x_{r})].$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/CompleteInputDeterminism.complete_input_agreement_excludes_deterministic_disagreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each decision input is constructed from the evidence concept and value, admission predicate, inference relation, value channel, action set, random seed, and actual anchor supplied by the source.

The decisioner is a relation whose right uniqueness is a public premise. Thus determinism is not installed by defining the decisioner as a function or by defining its inputs through the conclusion.

Right uniqueness proves agreement when all eight components coincide. The second public conjunct is its componentwise contrapositive: unequal related decisions identify at least one unequal input layer.

The qualitative remark about ease of resolving disagreement has no source predicate and is not asserted as a universal theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/CompleteInputDeterminism.complete_input_agreement_excludes_deterministic_disagreement`
