# Multi-Target Defect Graph Coloring

## Abstract

Joint-target defect graphs are component unions, with chromatic minimum repair.

**Theorem 1.1 (Joint defect graph union and minimum repair labels).**

$$\begin{gathered}\forall X, Index, Current: \operatorname{Type},\\{}Target: Index \to \operatorname{Type},\\{}[\operatorname{Fintype}(X)],\\{}current: \operatorname{Concept}\left(X, Current\right),\\{}targets: (\forall index: Index, \operatorname{Concept}\left(X, Target(index)\right)),\\{}(\operatorname{defectGraph}\left(current, \operatorname{jointTarget}\left(targets\right)\right) = \operatorname{iSup}\left(index: Index, \operatorname{defectGraph}\left(current, targets(index)\right)\right)) \land\\{}(\operatorname{minimumRepairLabels}\left(current, \operatorname{jointTarget}\left(targets\right)\right) = \operatorname{chromaticNumber}\left(\operatorname{iSup}\left(index: Index, \operatorname{defectGraph}\left(current, targets(index)\right)\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/MultiTargetDefectGraphColoring.joint_target_defect_graph_and_minimum_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier, the canonical defect graph of a dependent joint target is the indexed supremum of the component defect graphs.

The same graph equality identifies the least number of finite repair labels with the chromatic number of that indexed supremum.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/MultiTargetDefectGraphColoring.joint_target_defect_graph_and_minimum_labels`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/DefectRelationMinimumColoring](DefectRelationMinimumColoring.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology](../ObservationTopology/MultiTargetObservationTopology.md)
