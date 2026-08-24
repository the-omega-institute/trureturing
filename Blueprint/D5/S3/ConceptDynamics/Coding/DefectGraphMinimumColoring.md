# Defect Graph Minimum Coloring

## Abstract

Minimum defect-graph coloring computes the exact finite repair-label count.

**Theorem 1.1 (Minimum repair labels equal chromatic number and fiber diversity).**

$$\begin{gathered}\forall X, B, Y: \operatorname{Type},\\{}[\operatorname{Fintype}(X)],\\{}C: X \to B, T: X \to Y,\\{}(\forall m \in \mathbb{N}, \operatorname{RepairLabelFeasible}\left(C, T, m\right) \iff \operatorname{Colorable}\left(\operatorname{defectGraph}\left(C, T\right), m\right)) \land\\{}(\operatorname{minimumRepairLabels}\left(C, T\right) = \operatorname{chromaticNumber}\left(\operatorname{defectGraph}\left(C, T\right)\right)) \land\\{}(\operatorname{chromaticNumber}\left(\operatorname{defectGraph}\left(C, T\right)\right) = \operatorname{effectiveWorstFiberDiversity}\left(C, T\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.minimum_repair_labels_eq_chromatic_eq_fiber_diversity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is finite. The concept and target codomains need not be finite because the fiber maximum is taken over the canonical effective image of the concept readout.

The defect graph is constructed directly: two states are adjacent when their concept values agree and their target values differ. A finite repair label is feasible exactly when it is a proper coloring of this graph.

The least label count is selected from that feasibility test. The frozen sharp label theorem identifies it with the largest number of target values in an effective concept fiber, while the pinned coloring API identifies the same minimum with the graph's chromatic number.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.minimum_repair_labels_eq_chromatic_eq_fiber_diversity`
- Dependency: [D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount](../Appeal/MinimalAppealLabelCount.md)
