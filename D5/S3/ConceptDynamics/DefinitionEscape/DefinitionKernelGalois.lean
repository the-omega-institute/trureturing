/- GID: D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Family kernels form a Galois connection detecting primitive and productive escape. -/

import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw

/- Library-search audit trail (2026-08-24):
   * `JointFaithfulnessLeibnizCriterion` supplies the canonical `jointReadout`,
     `conceptKernel`, and `jointKernel` carriers.
   * `BlindKernelObstruction` supplies the canonical `blindResidual` and
     `languageExtension` carriers.
   * `ResidualJoinLaw` supplies the one-definition residual intersection law.
   * Repository searches found no Galois connection between definition families
     and source relations, no induced semantic closure operator, and no public
     equality identifying full-language defects with the blind residual. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction

/-- Readouts invariant on a supplied relation. -/
def RelationInvariantReadouts
    {X Output : Type*} (relation : Set (X × X)) :
    Set (Concept X Output) :=
  {readout | ∀ ⦃left right : X⦄,
    (left, right) ∈ relation → readout left = readout right}

/-- The semantic closure of a definition family consists of every output-valued
readout constant on the family's common kernel. -/
def SemanticClosure
    {X InputOutput Output : Type*}
    (Gamma : Set (Concept X InputOutput)) :
    Set (Concept X Output) :=
  RelationInvariantReadouts
    (jointKernel (fun definition : Gamma => definition.1))

/-- Same-codomain semantic closure. -/
def DefinitionClosure
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    Set (Concept X Output) :=
  SemanticClosure Gamma

/-- A candidate is a primitive escape when it separates a pair that every
definition in the current family identifies. -/
def PrimitiveEscape
    {X InputOutput Output : Type*}
    (Gamma : Set (Concept X InputOutput))
    (candidate : Concept X Output) : Prop :=
  candidate ∉ SemanticClosure Gamma

/-- A candidate is productive for a target when it separates a pair in the
target-relevant blind residual. -/
def ProductiveSeparation
    {X Current InputOutput Target Output : Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current) (target : Concept X Target)
    (candidate : Concept X Output) : Prop :=
  ∃ left right,
    (left, right) ∈ blindResidual Gamma current target ∧
      candidate left ≠ candidate right

/-- Definition families and source relations form a contravariant Galois
connection: every family member is invariant on a relation exactly when that
relation lies in the family's common kernel. -/
theorem definition_relation_galois
    {X Output : Type*}
    (Gamma : Set (Concept X Output)) (relation : Set (X × X)) :
    Gamma ⊆ RelationInvariantReadouts relation ↔
      relation ⊆ jointKernel (fun definition : Gamma => definition.1) := by
  constructor
  · intro invariant pair pairInRelation
    apply Set.mem_iInter.2
    intro definition
    change (definition.1 : X → Output) pair.1 = definition.1 pair.2
    exact invariant definition.2 pairInRelation
  · intro relationInKernel definition definitionInGamma left right pairInRelation
    have pairInJointKernel := relationInKernel pairInRelation
    have pairForDefinition :=
      Set.mem_iInter.1 pairInJointKernel ⟨definition, definitionInGamma⟩
    exact pairForDefinition

/-- Enlarging a definition family can only shrink its common kernel. -/
theorem jointKernel_antitone
    {X Output : Type*} {Gamma Delta : Set (Concept X Output)}
    (subset : Gamma ⊆ Delta) :
    jointKernel (fun definition : Delta => definition.1) ⊆
      jointKernel (fun definition : Gamma => definition.1) := by
  intro pair pairInDelta
  apply Set.mem_iInter.2
  intro definition
  exact Set.mem_iInter.1 pairInDelta
    ⟨definition.1, subset definition.2⟩

/-- Every current definition belongs to the semantic closure it generates. -/
theorem definitionClosure_extensive
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    Gamma ⊆ DefinitionClosure Gamma := by
  intro definition definitionInGamma left right pairInKernel
  exact Set.mem_iInter.1 pairInKernel ⟨definition, definitionInGamma⟩

/-- Semantic closure is monotone in the generating family. -/
theorem definitionClosure_mono
    {X Output : Type*} {Gamma Delta : Set (Concept X Output)}
    (subset : Gamma ⊆ Delta) :
    DefinitionClosure Gamma ⊆ DefinitionClosure Delta := by
  intro definition invariant left right pairInDelta
  exact invariant
    (jointKernel_antitone subset pairInDelta)

/-- Closing a definition family does not change its common kernel. -/
theorem jointKernel_definitionClosure
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    jointKernel
        (fun definition : DefinitionClosure Gamma => definition.1) =
      jointKernel (fun definition : Gamma => definition.1) := by
  apply Set.Subset.antisymm
  · exact jointKernel_antitone (definitionClosure_extensive Gamma)
  · intro pair pairInKernel
    apply Set.mem_iInter.2
    intro definition
    exact definition.2 pairInKernel

/-- Same-codomain semantic closure is idempotent. -/
theorem definitionClosure_idempotent
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    DefinitionClosure (DefinitionClosure Gamma) =
      DefinitionClosure Gamma := by
  unfold DefinitionClosure SemanticClosure
  exact congrArg RelationInvariantReadouts
    (jointKernel_definitionClosure Gamma)

/-- Membership in semantic closure is pointwise constancy on all pairs
indistinguishable by the complete definition family. -/
theorem mem_semanticClosure_iff_fiber_constant
    {X InputOutput Output : Type*}
    (Gamma : Set (Concept X InputOutput))
    (target : Concept X Output) :
    target ∈ SemanticClosure Gamma ↔
      ∀ ⦃left right : X⦄,
        (∀ definition : Gamma,
          definition.1 left = definition.1 right) →
        target left = target right := by
  constructor
  · intro invariant left right allEqual
    apply invariant
    simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
    exact allEqual
  · intro fiberConstant left right pairInKernel
    apply fiberConstant
    simpa only [jointKernel, conceptKernel, Set.mem_iInter,
      Set.mem_setOf_eq] using pairInKernel

/-- On an inhabited source, semantic-closure membership is exactly
factorization through the full joint readout. -/
theorem mem_semanticClosure_iff_factors
    {X InputOutput Output : Type*} [Nonempty X]
    (Gamma : Set (Concept X InputOutput))
    (target : Concept X Output) :
    target ∈ SemanticClosure Gamma ↔
      Refines target
        (jointReadout (fun definition : Gamma => definition.1)) := by
  constructor
  · intro invariant
    apply (target_recovery_criterion
      (jointReadout (fun definition : Gamma => definition.1)) target).1.mpr
    intro left right jointEqual
    apply (mem_semanticClosure_iff_fiber_constant Gamma target).1 invariant
    intro definition
    exact congrFun jointEqual definition
  · rintro ⟨recover, recovery⟩
    apply (mem_semanticClosure_iff_fiber_constant Gamma target).2
    intro left right allEqual
    have jointEqual :
        jointReadout (fun definition : Gamma => definition.1) left =
          jointReadout (fun definition : Gamma => definition.1) right := by
      funext definition
      exact allEqual definition
    rw [recovery]
    exact congrArg recover jointEqual

/-- Failure of semantic-closure membership has a concrete common-kernel
witness. -/
theorem not_mem_semanticClosure_iff_kernel_witness
    {X InputOutput Output : Type*}
    (Gamma : Set (Concept X InputOutput))
    (target : Concept X Output) :
    target ∉ SemanticClosure Gamma ↔
      ∃ left right,
        (∀ definition : Gamma,
          definition.1 left = definition.1 right) ∧
        target left ≠ target right := by
  classical
  constructor
  · intro outside
    by_contra noWitness
    apply outside
    apply (mem_semanticClosure_iff_fiber_constant Gamma target).2
    intro left right allEqual
    by_contra targetDifferent
    exact noWitness ⟨left, right, allEqual, targetDifferent⟩
  · rintro ⟨left, right, allEqual, targetDifferent⟩ inside
    exact targetDifferent
      ((mem_semanticClosure_iff_fiber_constant Gamma target).1
        inside allEqual)

/-- Productive separation is necessarily primitive: splitting a blind residual
pair escapes the complete semantic closure of the old definition family. -/
theorem productiveSeparation_implies_primitiveEscape
    {X Current InputOutput Target Output : Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current) (target : Concept X Target)
    (candidate : Concept X Output)
    (productive : ProductiveSeparation Gamma current target candidate) :
    PrimitiveEscape Gamma candidate := by
  rcases productive with ⟨left, right, pairInBlind, candidateDifferent⟩
  apply (not_mem_semanticClosure_iff_kernel_witness Gamma candidate).2
  refine ⟨left, right, ?_, candidateDifferent⟩
  simpa only [blindResidual, Set.mem_inter_iff, jointKernel,
    conceptKernel, Set.mem_iInter, Set.mem_setOf_eq] using pairInBlind.2

/-- The blind residual is empty exactly when every target defect pair is
separated by at least one member of the definition family. -/
theorem blindResidual_empty_iff_pointwise_separator
    {X Current InputOutput Target : Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current) (target : Concept X Target) :
    blindResidual Gamma current target = ∅ ↔
      ∀ ⦃left right : X⦄,
        (left, right) ∈ defectRelation current target →
          ∃ definition : Gamma,
            definition.1 left ≠ definition.1 right := by
  classical
  constructor
  · intro emptyBlind left right pairInDefect
    by_contra noSeparator
    have allEqual : ∀ definition : Gamma,
        definition.1 left = definition.1 right := by
      intro definition
      by_contra different
      exact noSeparator ⟨definition, different⟩
    have pairInBlind :
        (left, right) ∈ blindResidual Gamma current target := by
      refine ⟨pairInDefect, ?_⟩
      simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
      exact allEqual
    rw [emptyBlind] at pairInBlind
    exact pairInBlind
  · intro separates
    ext pair
    constructor
    · rintro ⟨pairInDefect, pairInKernel⟩
      rcases separates pairInDefect with ⟨definition, different⟩
      apply different
      exact Set.mem_iInter.1 pairInKernel definition
    · intro impossible
      exact impossible.elim

/-- Public full-language identity: adjoining the joint readout of every
definition leaves exactly the blind residual. -/
theorem languageExtension_defect_eq_blindResidual
    {X Current InputOutput Target : Type*}
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current) (target : Concept X Target) :
    defectRelation
        (languageExtension current
          (fun definition : Gamma => definition.1)) target =
      blindResidual Gamma current target := by
  ext pair
  change
    (((current pair.1,
          jointReadout (fun definition : Gamma => definition.1) pair.1) =
        (current pair.2,
          jointReadout (fun definition : Gamma => definition.1) pair.2)) ∧
        target pair.1 ≠ target pair.2) ↔
      ((current pair.1 = current pair.2 ∧
        target pair.1 ≠ target pair.2) ∧
        pair ∈ jointKernel
          (fun definition : Gamma => definition.1))
  constructor
  · rintro ⟨extensionEqual, targetDifferent⟩
    refine ⟨⟨congrArg Prod.fst extensionEqual, targetDifferent⟩, ?_⟩
    have jointEqual := congrArg Prod.snd extensionEqual
    simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
    intro definition
    exact congrFun jointEqual definition
  · rintro ⟨⟨currentEqual, targetDifferent⟩, pairInKernel⟩
    have jointEqual :
        jointReadout (fun definition : Gamma => definition.1) pair.1 =
          jointReadout (fun definition : Gamma => definition.1) pair.2 := by
      funext definition
      exact Set.mem_iInter.1 pairInKernel definition
    exact ⟨Prod.ext currentEqual jointEqual, targetDifferent⟩

#print axioms definition_relation_galois
#print axioms definitionClosure_idempotent
#print axioms mem_semanticClosure_iff_factors
#print axioms productiveSeparation_implies_primitiveEscape
#print axioms languageExtension_defect_eq_blindResidual

end D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
