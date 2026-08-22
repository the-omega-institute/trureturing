# Partition and General Negative-Introspection Contrast

## Abstract

Partition knowledge satisfies negative introspection, but general topological knowledge need not.

**Theorem 1.1 (Negative introspection holds for partitions but fails in general).**

$$\begin{gathered}(\forall X, B: \operatorname{Type}, C: X \to B, P\subset X,\\{}\operatorname{IsOpen}_{\tau_{C}}(X \setminus \operatorname{K}\left(C, P\right)) \land\\{}\forall x\in X, \neg(x\in \operatorname{K}\left(C, P\right)) \Rightarrow x\in \operatorname{K}\left(C, X \setminus \operatorname{K}\left(C, P\right)\right))\\{}\land \neg(\forall x\in Prop, \neg(x\in \operatorname{Int}_{\tau_{S}}(\{true\})) \Rightarrow x\in \operatorname{Int}_{\tau_{S}}(Prop \setminus \operatorname{Int}_{\tau_{S}}(\{true\}))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Epistemic/PartitionAndGeneralNegativeIntrospectionContrast.partition_and_general_negative_introspection_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary state and coordinate types, the readout and predicate are independent source primitives. The knowledge set and topology are constructed from the readout exactly as in the frozen family module.

The first public conjunct states that knowledge failure is open in the readout-partition topology and is known throughout the failing readout fiber.

The second public conjunct is an explicit countermodel for unrestricted topological knowledge. In Mathlib's Sierpinski topology on Prop, the interior of the singleton true predicate is that singleton, while false is not interior to its complement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Epistemic/PartitionAndGeneralNegativeIntrospectionContrast.partition_and_general_negative_introspection_contrast`
