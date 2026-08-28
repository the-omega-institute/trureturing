/- GID: D5/S3/ConceptDynamics/Topology/ObservationEscapeTopology
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/ObservationEscapeTopology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Kernel refinement and productive separation include empty-source primitive escape. -/

import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
import D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
import D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
import D5.S3.ConceptDynamics.ObservationTopology.SemanticClosureTopologyInvariance
import D5.S3.ConceptDynamics.ObservationTopology.PrimitiveEscapeStrictRefinement
import D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization

/- Library-search audit trail (2026-08-25):
   * The frozen ObservationTopology batch supplies the canonical partition
     kernel, residual separation, target continuity, semantic-closure invariance,
     and inhabited primitive-refinement theorems; exact PR duplicates were deleted.
   * `partitionTopology` remains the sole reducible carrier from
     `PartitionKnowledgeNegativeIntrospection`; no local carrier is introduced.
   * No frozen counterpart exports generic one-way kernel refinement, the joint
     kernel bridge, the productive split bundle, or the empty-source strengthening. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.ObservationEscapeTopology

open Set TopologicalSpace
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Epistemic.PartitionKnowledgeNegativeIntrospection
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.ObservationTopology.PartitionTopologyKernel
open D5.S3.ConceptDynamics.ObservationTopology.ResidualSeparationTopology
open D5.S3.ConceptDynamics.ObservationTopology.PrimitiveEscapeStrictRefinement
open D5.S3.ConceptDynamics.ObservationTopology.TargetContinuityFactorization

universe u v w z

/-- Equality of a joint readout is membership in the imported common kernel. -/
theorem jointReadout_eq_iff_jointKernel
    {Index : Type u} {X : Type v} {Value : Index -> Type w}
    (readouts : forall index, X -> Value index) (left right : X) :
    jointReadout readouts left = jointReadout readouts right ↔
      (left, right) ∈ jointKernel readouts := by
  simp only [jointReadout, jointKernel, conceptKernel, Set.mem_iInter,
    Set.mem_setOf_eq, funext_iff]

/-- Kernel inclusion makes the finer partition topology finer in Mathlib's
 reversed topology order. -/
theorem partitionTopology_le_of_kernel
    {X : Type u} {Coarse : Type v} {Fine : Type w}
    (coarse : Concept X Coarse) (fine : Concept X Fine)
    (kernel : forall {left right},
      fine left = fine right -> coarse left = coarse right) :
    partitionTopology fine ≤ partitionTopology coarse := by
  letI : TopologicalSpace Coarse := ⊥
  letI : DiscreteTopology Coarse := ⟨rfl⟩
  letI : TopologicalSpace Fine := ⊥
  letI : DiscreteTopology Fine := ⟨rfl⟩
  change TopologicalSpace.induced fine ⊥ ≤ TopologicalSpace.induced coarse ⊥
  intro states statesOpen
  rw [isOpen_induced_iff] at statesOpen ⊢
  rcases statesOpen with ⟨coarseCoordinates, _coarseOpen, rfl⟩
  refine ⟨{coordinate | ∃ state,
      fine state = coordinate ∧ coarse state ∈ coarseCoordinates},
    isOpen_discrete _, ?_⟩
  ext state
  constructor
  · rintro ⟨witness, sameFine, witnessCoarse⟩
    change coarse state ∈ coarseCoordinates
    have sameCoarse : coarse witness = coarse state := kernel sameFine
    rw [← sameCoarse]
    exact witnessCoarse
  · intro stateInPreimage
    change fine state ∈ {coordinate | ∃ witness,
      fine witness = coordinate ∧ coarse witness ∈ coarseCoordinates}
    exact ⟨state, rfl, stateInPreimage⟩

/-- Joining one candidate to the current complete family always refines the
 old family topology. -/
theorem candidate_join_partitionTopology_le
    {X : Type u} {InputOutput : Type v} {Output : Type w}
    (Gamma : Set (Concept X InputOutput))
    (candidate : Concept X Output) :
    partitionTopology
        (conceptJoin
          (jointReadout (fun definition : Gamma => definition.1)) candidate) ≤
      partitionTopology
        (jointReadout (fun definition : Gamma => definition.1)) := by
  apply partitionTopology_le_of_kernel
  intro left right joinedEqual
  exact congrArg Prod.fst joinedEqual

private theorem strictObservationRefinement_iff_lt
    {X : Type u} (coarse fine : TopologicalSpace X) :
    StrictObservationRefinement coarse fine ↔ fine < coarse := by
  constructor
  · rintro ⟨coarseOpenInFine, witness, witnessOpenFine, witnessNotOpenCoarse⟩
    apply lt_of_le_not_ge
    · exact coarseOpenInFine
    · intro fineOpenInCoarse
      exact witnessNotOpenCoarse (fineOpenInCoarse witness witnessOpenFine)
  · intro strict
    refine ⟨le_of_lt strict, ?_⟩
    by_contra noWitness
    apply not_le_of_gt strict
    intro states statesOpenFine
    by_contra statesNotOpenCoarse
    exact noWitness ⟨states, statesOpenFine, statesNotOpenCoarse⟩

/-- Primitive escape is strict partition refinement even for an empty source. -/
theorem primitiveEscape_iff_strict_partition_refinement
    {X : Type u} {InputOutput : Type v} {Output : Type w}
    (Gamma : Set (Concept X InputOutput))
    (candidate : Concept X Output) :
    PrimitiveEscape Gamma candidate ↔
      partitionTopology
          (conceptJoin
            (jointReadout (fun definition : Gamma => definition.1)) candidate) <
        partitionTopology
          (jointReadout (fun definition : Gamma => definition.1)) := by
  cases isEmpty_or_nonempty X with
  | inl sourceEmpty =>
      letI : IsEmpty X := sourceEmpty
      constructor
      · intro primitive
        exfalso
        apply primitive
        intro left right _pairInKernel
        exact isEmptyElim left
      · intro strictRefinement
        have topologyEquality :
            partitionTopology
                (conceptJoin
                  (jointReadout (fun definition : Gamma => definition.1)) candidate) =
              partitionTopology
                (jointReadout (fun definition : Gamma => definition.1)) :=
          Subsingleton.elim _ _
        exact False.elim ((ne_of_lt strictRefinement) topologyEquality)
  | inr sourceNonempty =>
      letI : Nonempty X := sourceNonempty
      simpa [extendedFamilyReadout] using
        (primitiveEscape_iff_strict_topology_refinement Gamma candidate).trans
          (strictObservationRefinement_iff_lt _ _)

/-- Productive separation is exactly a target-defect pair left inseparable by
 the complete language and separated by the candidate. -/
theorem productiveSeparation_iff_topological_target_split
    {X : Type u} {Current : Type v} {InputOutput : Type w}
    {Target : Type z} {Output : Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current) (target : Concept X Target)
    (candidate : Concept X Output) :
    ProductiveSeparation Gamma current target candidate ↔
      ∃ left right,
        @Inseparable X (partitionTopology current) left right ∧
          ¬@Inseparable X (partitionTopology target) left right ∧
          @Inseparable X
            (partitionTopology
              (jointReadout (fun definition : Gamma => definition.1)))
            left right ∧
          ¬@Inseparable X (partitionTopology candidate) left right := by
  constructor
  · rintro ⟨left, right, pairInBlind, candidateDifferent⟩
    have targetSplit :=
      (defectRelation_iff_topological_separation_deficit
        current target left right).1 pairInBlind.1
    refine ⟨left, right, targetSplit.1, targetSplit.2, ?_, ?_⟩
    · apply (partition_inseparable_iff_kernel
        (jointReadout (fun definition : Gamma => definition.1)) left right).2
      rw [jointReadout_eq_iff_jointKernel]
      exact pairInBlind.2
    · intro candidateInseparable
      exact candidateDifferent
        ((partition_inseparable_iff_kernel candidate left right).1
          candidateInseparable)
  · rintro ⟨left, right, currentInseparable, targetSeparable, languageInseparable,
      candidateSeparable⟩
    have pairInDefect : (left, right) ∈ defectRelation current target :=
      (defectRelation_iff_topological_separation_deficit
        current target left right).2 ⟨currentInseparable, targetSeparable⟩
    refine ⟨left, right, ⟨pairInDefect, ?_⟩, ?_⟩
    · rw [← jointReadout_eq_iff_jointKernel]
      exact (partition_inseparable_iff_kernel
        (jointReadout (fun definition : Gamma => definition.1)) left right).1
          languageInseparable
    · intro candidateEqual
      exact candidateSeparable
        ((partition_inseparable_iff_kernel candidate left right).2
          candidateEqual)

/-- Exact closure of a target residual is continuity in the target partition
 topology, and a nonempty residual is a concrete topological separation defect. -/
theorem residual_empty_iff_continuous_and_nonempty_iff_separation
    {X : Type u} {Current : Type v} {Target : Type w} [Nonempty X]
    (current : Concept X Current) (target : Concept X Target) :
    (defectRelation current target = ∅ ↔
      @Continuous X Target (partitionTopology current) ⊥ target) ∧
    ((defectRelation current target).Nonempty ↔
      ∃ left right,
        @Inseparable X (partitionTopology current) left right ∧
          ¬@Inseparable X (partitionTopology target) left right) := by
  constructor
  · exact (target_recovery_criterion current target).2.2.1.trans
      (target_factors_iff_continuous_partition current target)
  · constructor
    · rintro ⟨pair, pairDefect⟩
      exact ⟨pair.1, pair.2,
        (defectRelation_iff_topological_separation_deficit
          current target pair.1 pair.2).1
          pairDefect⟩
    · rintro ⟨left, right, separated⟩
      exact ⟨(left, right),
        (defectRelation_iff_topological_separation_deficit
          current target left right).2 separated⟩

#print axioms jointReadout_eq_iff_jointKernel
#print axioms partitionTopology_le_of_kernel
#print axioms primitiveEscape_iff_strict_partition_refinement
#print axioms productiveSeparation_iff_topological_target_split

end D5.S3.ConceptDynamics.Topology.ObservationEscapeTopology
