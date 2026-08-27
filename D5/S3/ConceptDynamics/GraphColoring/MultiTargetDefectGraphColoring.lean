/- GID: D5/S3/ConceptDynamics/GraphColoring/MultiTargetDefectGraphColoring
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/MultiTargetDefectGraphColoring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint-target defect graphs are component unions, with chromatic minimum repair. -/

import D5.S3.ConceptDynamics.GraphColoring.DefectRelationMinimumColoring
import D5.S3.ConceptDynamics.ObservationTopology.MultiTargetObservationTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.MultiTargetDefectGraphColoring

open D5.S3.ConceptDynamics.Coding.DefectGraphMinimumColoring
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.GraphColoring.DefectRelationMinimumColoring
open D5.S3.ConceptDynamics.ObservationTopology.MultiTargetObservationTopology
open D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

/-- The defect graph of a joint target is the indexed union of its component
graphs, and its least finite repair-label count is that union's chromatic number. -/
theorem joint_target_defect_graph_and_minimum_labels
    {X Index Current : Type*} {Target : Index → Type*} [Fintype X]
    (current : Concept X Current)
    (targets : ∀ index, Concept X (Target index)) :
    DefectRelationMinimumColoring.defectGraph current (jointTarget targets) =
        ⨆ index, DefectRelationMinimumColoring.defectGraph current (targets index) ∧
      (minimumRepairLabels current (jointTarget targets) : ℕ∞) =
        (⨆ index,
          DefectRelationMinimumColoring.defectGraph current (targets index)).chromaticNumber := by
  have graphUnion :
      DefectRelationMinimumColoring.defectGraph current (jointTarget targets) =
        ⨆ index, DefectRelationMinimumColoring.defectGraph current (targets index) := by
    ext left right
    simp only [DefectRelationMinimumColoring.defectGraph, SimpleGraph.iSup_adj]
    simpa only [← defectRelation_eq_separationDeficit] using
      (mem_jointTarget_separationDeficit_iff current targets (left, right))
  refine ⟨graphUnion, ?_⟩
  calc
    (minimumRepairLabels current (jointTarget targets) : ℕ∞) =
        (DefectRelationMinimumColoring.defectGraph
          current (jointTarget targets)).chromaticNumber :=
      (DefectRelationMinimumColoring.minimum_repair_labels_eq_chromatic_eq_fiber_diversity
        current (jointTarget targets)).2.1
    _ = (⨆ index,
        DefectRelationMinimumColoring.defectGraph current (targets index)).chromaticNumber :=
      congrArg (fun graph : SimpleGraph X => graph.chromaticNumber) graphUnion

#print axioms joint_target_defect_graph_and_minimum_labels

end D5.S3.ConceptDynamics.GraphColoring.MultiTargetDefectGraphColoring
