# Typed Definition Graph Slice

## Abstract

A dependency slice can strictly enlarge its target set.

**Theorem 1.1 (Dependency slicing can strictly add prerequisites).**

$$twoNodeTargets \subset \operatorname{dependencySlice}\left(twoNodeDefinitionGraph, twoNodeTargets\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/TypedDefinitionGraphSlice.dependencySlice_strict_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the concrete two-node typed definition graph, false is a direct prerequisite of true and the target set contains only true. The reflexive-transitive predecessor slice therefore also contains false.

This witnesses proper containment rather than only the general inclusion of targets in their dependency slice.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/TypedDefinitionGraphSlice.dependencySlice_strict_witness`
- Dependency: [D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure](PrerequisiteClosure.md)
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
