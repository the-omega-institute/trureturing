/- GID: D5/S3/ConceptDynamics/Topology/ObservationEscapeTopology
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observation kernels, topology, target residuals, closure, and primitive escape coincide exactly. -/

import D5.S3.ConceptDynamics.Epistemic.FiberInteriorEquivalence
import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
import Mathlib.Topology.Inseparable

/- Library-search audit trail (2026-08-25):
   * `partitionTopology`, `jointReadout`, `jointKernel`, `defectRelation`,
     `SemanticClosure`, `PrimitiveEscape`, and `ProductiveSeparation` are reused
     from their frozen canonical modules rather than redeclared.
   * Pinned Mathlib supplies `Inseparable`, induced-topology opening laws, and
     discrete-output separation. Repository searches found no accepted theorem
     identifying all of kernel equality, topological inseparability, continuity,
     semantic-closure invariance, and strict primitive refinement.
   * This module contains only carrier-generic topology and logic. It assigns no
     scientific worth, repository status, workflow meaning, or agent semantics. -/

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

universe u v w z

/-- Two states are topologically inseparable in the discrete-output partition
 topology exactly when the readout gives them the same coordinate. -/
theorem partition_inseparable_iff_kernel
    {X : Type u} {Output : Type v}
    (readout : Concept X Output) (left right : X) :
    @Inseparable X (partitionTopology readout) left right ↔
      readout left = readout right := by
  letI : TopologicalSpace Output := ⊥
  letI : DiscreteTopology Output := ⟨rfl⟩
  letI : TopologicalSpace X := partitionTopology readout
  constructor
  · intro inseparable
    let fiber : Set X := {state | readout state = readout left}
    have fiberOpen : IsOpen fiber := by
      rw [partitionTopology, isOpen_induced_iff]
      refine ⟨{readout left}, isOpen_discrete _, ?_⟩
      ext state
      simp [fiber]
    have leftInFiber : left ∈ fiber := by simp [fiber]
    exact ((inseparable.mem_open_iff fiberOpen).1 leftInFiber).symm
  · intro sameCoordinate
    apply inseparable_iff_forall_isOpen.2
    intro states statesOpen
    rw [partitionTopology, isOpen_induced_iff] at statesOpen
    rcases statesOpen with ⟨coordinates, _coordinatesOpen, rfl⟩
    simp only [Set.mem_preimage]
    rw [sameCoordinate]

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
  intro states statesOpen
  rw [partitionTopology, isOpen_induced_iff] at statesOpen ⊢
  rcases statesOpen with ⟨coarseCoordinates, _coarseOpen, rfl⟩
  refine ⟨{coordinate | ∃ state,
      fine state = coordinate ∧ coarse state ∈ coarseCoordinates},
    isOpen_discrete _, ?_⟩
  ext state
  constructor
  · intro stateInPreimage
    change fine state ∈ {coordinate | ∃ witness,
      fine witness = coordinate ∧ coarse witness ∈ coarseCoordinates}
    exact ⟨state, rfl, stateInPreimage⟩
  · rintro ⟨witness, sameFine, witnessCoarse⟩
    change coarse state ∈ coarseCoordinates
    have sameCoarse : coarse witness = coarse state := kernel sameFine
    rw [← sameCoarse]
    exact witnessCoarse

/-- Two discrete-output partition topologies are equal exactly when their
 kernels agree pointwise. -/
theorem partitionTopology_eq_of_kernel_iff
    {X : Type u} {Left : Type v} {Right : Type w}
    (leftReadout : Concept X Left) (rightReadout : Concept X Right)
    (kernel : forall left right,
      leftReadout left = leftReadout right ↔
        rightReadout left = rightReadout right) :
    partitionTopology leftReadout = partitionTopology rightReadout := by
  apply le_antisymm
  · exact partitionTopology_le_of_kernel rightReadout leftReadout
      (fun sameLeft => (kernel _ _).mp sameLeft)
  · exact partitionTopology_le_of_kernel leftReadout rightReadout
      (fun sameRight => (kernel _ _).mpr sameRight)

/-- A target defect is exactly present inseparability together with target
 separability. -/
theorem defectRelation_iff_topological_separation
    {X : Type u} {Current : Type v} {Target : Type w}
    (current : Concept X Current) (target : Concept X Target)
    (pair : X × X) :
    pair ∈ defectRelation current target ↔
      @Inseparable X (partitionTopology current) pair.1 pair.2 ∧
        ¬@Inseparable X (partitionTopology target) pair.1 pair.2 := by
  simp only [defectRelation, Set.mem_setOf_eq,
    partition_inseparable_iff_kernel]

/-- A target is continuous from the current partition topology to a discrete
 codomain exactly when it is constant on every current readout fiber. -/
theorem partitionContinuous_iff_fiber_constant
    {X : Type u} {Current : Type v} {Target : Type w}
    (current : Concept X Current) (target : Concept X Target) :
    @Continuous X Target (partitionTopology current) ⊥ target ↔
      forall {left right}, current left = current right ->
        target left = target right := by
  letI : TopologicalSpace X := partitionTopology current
  letI : TopologicalSpace Target := ⊥
  letI : DiscreteTopology Target := ⟨rfl⟩
  constructor
  · intro continuous left right sameCurrent
    have currentInseparable : Inseparable left right :=
      (partition_inseparable_iff_kernel current left right).2 sameCurrent
    exact (currentInseparable.map continuous).eq
  · intro fiberConstant
    rw [continuous_def]
    intro targetStates _targetStatesOpen
    rw [partitionTopology, isOpen_induced_iff]
    refine ⟨{coordinate | ∃ state,
      current state = coordinate ∧ target state ∈ targetStates},
      isOpen_discrete _, ?_⟩
    ext state
    constructor
    · intro stateInTarget
      change current state ∈ {coordinate | ∃ witness,
        current witness = coordinate ∧ target witness ∈ targetStates}
      exact ⟨state, rfl, stateInTarget⟩
    · rintro ⟨witness, sameCurrent, witnessInTarget⟩
      change target state ∈ targetStates
      have sameTarget : target witness = target state :=
        fiberConstant sameCurrent
      rw [← sameTarget]
      exact witnessInTarget

/-- On an inhabited source, target factorization through a readout is exactly
 continuity from the readout partition topology to the discrete target. -/
theorem target_factors_iff_partitionContinuous
    {X : Type u} {Current : Type v} {Target : Type w} [Nonempty X]
    (current : Concept X Current) (target : Concept X Target) :
    (∃ recover : Current -> Target, target = recover ∘ current) ↔
      @Continuous X Target (partitionTopology current) ⊥ target := by
  exact (target_recovery_criterion current target).1.trans
    (partitionContinuous_iff_fiber_constant current target).symm

/-- Adding every semantically recoverable readout changes neither the family
 kernel nor its induced observation topology. -/
theorem semanticClosure_partitionTopology_invariant
    {X : Type u} {Output : Type v}
    (Gamma : Set (Concept X Output)) :
    partitionTopology
        (jointReadout
          (fun definition : DefinitionClosure Gamma => definition.1)) =
      partitionTopology
        (jointReadout (fun definition : Gamma => definition.1)) := by
  apply partitionTopology_eq_of_kernel_iff
  intro left right
  rw [jointReadout_eq_iff_jointKernel, jointReadout_eq_iff_jointKernel,
    jointKernel_definitionClosure]

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

/-- Primitive definition escape is exactly strict refinement of the observation
 topology generated by the old complete language. -/
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
  classical
  let oldReadout : Concept X (Gamma -> InputOutput) :=
    jointReadout (fun definition : Gamma => definition.1)
  let newReadout : Concept X ((Gamma -> InputOutput) × Output) :=
    conceptJoin oldReadout candidate
  have refinement : partitionTopology newReadout ≤ partitionTopology oldReadout := by
    exact partitionTopology_le_of_kernel oldReadout newReadout
      (fun joinedEqual => congrArg Prod.fst joinedEqual)
  constructor
  · intro primitive
    rcases (not_mem_semanticClosure_iff_kernel_witness Gamma candidate).1 primitive with
      ⟨left, right, allDefinitionsEqual, candidateDifferent⟩
    have oldEqual : oldReadout left = oldReadout right := by
      funext definition
      exact allDefinitionsEqual definition
    have oldInseparable :
        @Inseparable X (partitionTopology oldReadout) left right :=
      (partition_inseparable_iff_kernel oldReadout left right).2 oldEqual
    have newNotInseparable :
        ¬@Inseparable X (partitionTopology newReadout) left right := by
      intro newInseparable
      have newEqual :=
        (partition_inseparable_iff_kernel newReadout left right).1
          newInseparable
      exact candidateDifferent (congrArg Prod.snd newEqual)
    have topologiesDifferent :
        partitionTopology newReadout ≠ partitionTopology oldReadout := by
      intro topologiesEqual
      apply newNotInseparable
      simpa [topologiesEqual] using oldInseparable
    exact lt_of_le_of_ne refinement topologiesDifferent
  · intro strictRefinement
    by_contra notPrimitive
    have candidateInside : candidate ∈ SemanticClosure Gamma := by
      simpa [PrimitiveEscape] using notPrimitive
    have sameKernel : forall left right,
        newReadout left = newReadout right ↔
          oldReadout left = oldReadout right := by
      intro left right
      constructor
      · intro newEqual
        exact congrArg Prod.fst newEqual
      · intro oldEqual
        apply Prod.ext oldEqual
        apply (mem_semanticClosure_iff_fiber_constant Gamma candidate).1
          candidateInside
        intro definition
        exact congrFun oldEqual definition
    have equalTopologies :
        partitionTopology newReadout = partitionTopology oldReadout :=
      partitionTopology_eq_of_kernel_iff newReadout oldReadout sameKernel
    exact strictRefinement.ne equalTopologies

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
        (left, right) ∈ defectRelation current target ∧
          @Inseparable X
            (partitionTopology
              (jointReadout (fun definition : Gamma => definition.1)))
            left right ∧
          ¬@Inseparable X (partitionTopology candidate) left right := by
  constructor
  · rintro ⟨left, right, pairInBlind, candidateDifferent⟩
    refine ⟨left, right, pairInBlind.1, ?_, ?_⟩
    · apply (partition_inseparable_iff_kernel
        (jointReadout (fun definition : Gamma => definition.1)) left right).2
      rw [jointReadout_eq_iff_jointKernel]
      exact pairInBlind.2
    · intro candidateInseparable
      exact candidateDifferent
        ((partition_inseparable_iff_kernel candidate left right).1
          candidateInseparable)
  · rintro ⟨left, right, pairInDefect, languageInseparable,
      candidateSeparable⟩
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
      (target_factors_iff_partitionContinuous current target)
  · constructor
    · rintro ⟨pair, pairDefect⟩
      exact ⟨pair.1, pair.2,
        (defectRelation_iff_topological_separation current target pair).1
          pairDefect⟩
    · rintro ⟨left, right, separated⟩
      exact ⟨(left, right),
        (defectRelation_iff_topological_separation current target
          (left, right)).2 separated⟩

#print axioms partition_inseparable_iff_kernel
#print axioms target_factors_iff_partitionContinuous
#print axioms semanticClosure_partitionTopology_invariant
#print axioms primitiveEscape_iff_strict_partition_refinement
#print axioms productiveSeparation_iff_topological_target_split

end D5.S3.ConceptDynamics.Topology.ObservationEscapeTopology
