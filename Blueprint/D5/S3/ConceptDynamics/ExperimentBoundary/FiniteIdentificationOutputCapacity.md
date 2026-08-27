# Finite Identification Output Capacity

## Abstract

A separating finite protocol family obeys effective-output capacity bounds.

**Theorem 1.1 (Effective outputs bound finite identification capacity).**

$$\forall X \in Type, P \in Type, O \in P \to Type, c \in \prod_{p: P} X \to O\left(p\right),\; \left(\operatorname{Finite}\left(X\right) \land \left(\operatorname{Nonempty}\left(X\right) \land \left(\operatorname{Fintype}\left(P\right) \land \operatorname{Injective}\left(\operatorname{jointReadout}\left(c\right)\right)\right)\right)\right) \Rightarrow \left(\operatorname{card}\left(X\right) \le \prod_{p\in P} \operatorname{card}\left(\operatorname{range}\left(c\left(p\right)\right)\right) \land \left(\log_{2}\left(\operatorname{card}\left(X\right)\right) \le \sum_{p\in P} \log_{2}\left(\operatorname{card}\left(\operatorname{range}\left(c\left(p\right)\right)\right)\right) \land \left(\forall m \in \mathbb{N},\; \left(1 < m \land \left(\forall p \in P,\; \operatorname{card}\left(\operatorname{range}\left(c\left(p\right)\right)\right) \le m\right)\right) \Rightarrow \operatorname{natCeil}\left(\log_{m}\left(\operatorname{card}\left(X\right)\right)\right) \le \operatorname{card}\left(P\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentBoundary/FiniteIdentificationOutputCapacity.finite_identification_output_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state-class carrier is finite and nonempty, the protocol carrier is a finite type, and each protocol may have its own output type. The canonical jointReadout map is required to be injective.

Each effective output count is the cardinality of the actual range of that protocol on the state classes. The displayed formula expands both Lean let-bindings rather than introducing alternate objects.

The three public conclusions are the product capacity bound, its base-two logarithmic form, and the uniform-output lower bound for every natural base strictly greater than one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/FiniteIdentificationOutputCapacity.finite_identification_output_capacity`
- Dependency: [D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound](../Experiment/FiniteIdentificationCapacityBound.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
