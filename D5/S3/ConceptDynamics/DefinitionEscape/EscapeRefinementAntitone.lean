/- GID: D5/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/EscapeRefinementAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining an observer family can only shrink defect and primitive escape. -/

import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
import D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting

/- Library-search audit trail (2026-09-01):
   * Repository search found the canonical dependent `jointReadout`,
     `conceptJoin`, and `defectRelation` carriers used in the finite-window law.
     The higher `defectRelation_antitone_of_refines` theorem has the same
     information-order direction, but its observation-topology module already
     depends on DefinitionEscape and cannot be imported back into this layer.
   * `DefinitionKernelGalois.jointKernel_antitone` is the exact homogeneous
     intersection-family law needed for the `PrimitiveEscape` consistency
     statement, so it is reused rather than reproved.
   * Pinned-library searches for intersection monotonicity found no theorem
     that subsumes the dependent subtype restriction in the first statement.
     That restriction is proved pointwise; no second escape carrier is added. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.EscapeRefinementAntitone

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- Enlarging a selected observer family can only shrink the target-sensitive
defect relation of its joint readout with a fixed baseline. -/
theorem escape_refinement_antitone
    {I X C Target : Type*} {V : I → Type*}
    {S S' : Set I} (subset : S ⊆ S')
    (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target) :
    defectRelation
        (conceptJoin q
          (jointReadout (fun item : S' => definitions item.1))) target ⊆
      defectRelation
        (conceptJoin q
          (jointReadout (fun item : S => definitions item.1))) target := by
  rintro ⟨left, right⟩ ⟨sameRefinedReadout, targetDifferent⟩
  refine ⟨?_, targetDifferent⟩
  change
    (q left, fun item : S => definitions item.1 left) =
      (q right, fun item : S => definitions item.1 right)
  have sameBaseline : q left = q right :=
    congrArg
      (fun value : C × ((item : S') → V item.1) => value.1)
      sameRefinedReadout
  have sameRestricted :
      (fun item : S => definitions item.1 left) =
        (fun item : S => definitions item.1 right) := by
    funext item
    exact congrFun
      (congrArg
        (fun value : C × ((item : S') → V item.1) => value.2)
        sameRefinedReadout)
      ⟨item.1, subset item.2⟩
  exact Prod.ext sameBaseline sameRestricted

/-- In the intersection-kernel presentation, enlarging a homogeneous observer
family can only shrink the set of candidates that escape its semantic closure. -/
theorem primitive_escape_refinement_antitone
    {X InputOutput Output : Type*}
    {Gamma Delta : Set (Concept X InputOutput)}
    (subset : Gamma ⊆ Delta) :
    {candidate : Concept X Output | PrimitiveEscape Delta candidate} ⊆
      {candidate : Concept X Output | PrimitiveEscape Gamma candidate} := by
  intro candidate candidateEscapesDelta candidateInGammaClosure
  apply candidateEscapesDelta
  intro left right pairInDeltaKernel
  exact candidateInGammaClosure
    (jointKernel_antitone subset pairInDeltaKernel)

#print axioms escape_refinement_antitone
#print axioms primitive_escape_refinement_antitone

end D5.S3.ConceptDynamics.DefinitionEscape.EscapeRefinementAntitone
