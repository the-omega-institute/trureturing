/- GID: D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A target defect is exactly a topological separation deficit. -/

import D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel

def separationDeficit
    {X Current Target : Type*} (current : Concept X Current)
    (target : Concept X Target) : Set (X × X) :=
  {pair | @Inseparable X (partitionTopology current) pair.1 pair.2 ∧
    ¬ @Inseparable X (partitionTopology target) pair.1 pair.2}

theorem defectRelation_eq_separationDeficit
    {X Current Target : Type*} (current : Concept X Current)
    (target : Concept X Target) :
    defectRelation current target = separationDeficit current target := by
  ext pair
  change (current pair.1 = current pair.2 ∧ target pair.1 ≠ target pair.2) <->
    (@Inseparable X (partitionTopology current) pair.1 pair.2 ∧
      ¬ @Inseparable X (partitionTopology target) pair.1 pair.2)
  rw [partition_inseparable_iff_kernel current,
    partition_inseparable_iff_kernel target]

theorem defectRelation_iff_topological_separation_deficit
    {X Current Target : Type*} (current : Concept X Current)
    (target : Concept X Target) (x y : X) :
    (x, y) ∈ defectRelation current target <->
      @Inseparable X (partitionTopology current) x y ∧
        ¬ @Inseparable X (partitionTopology target) x y := by
  rw [defectRelation_eq_separationDeficit]
  rfl

theorem separationDeficit_join_law
    {X Current Candidate Target : Type*}
    (current : Concept X Current) (candidate : Concept X Candidate)
    (target : Concept X Target) :
    separationDeficit (conceptJoin current candidate) target =
      separationDeficit current target ∩
        {pair : X × X |
          @Inseparable X (partitionTopology candidate) pair.1 pair.2} := by
  rw [← defectRelation_eq_separationDeficit (conceptJoin current candidate) target,
    ← defectRelation_eq_separationDeficit current target, residual_join_law]
  ext pair
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [partition_inseparable_iff_kernel candidate]
  change
    (pair ∈ defectRelation current target ∧
        candidate pair.1 = candidate pair.2) ↔
      (pair ∈ defectRelation current target ∧
        candidate pair.1 = candidate pair.2)
  rfl

#print axioms defectRelation_eq_separationDeficit
#print axioms separationDeficit_join_law
end D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
