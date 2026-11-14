import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.OriginExclusionSegmentRigidity
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.OriginExclusionSegmentRigidity

open _root_.D5.S3.Quantum.OriginExclusionSegmentRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private def leftClaim (t b : ℝ) : Prop := b ^ 2 ≤ t * (1 - t)
private def rightClaim (t b : ℝ) : Prop :=
  (t - (1 / 2 : ℝ)) ^ 2 + b ^ 2 ≤ (1 / 2 : ℝ) ^ 2

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun _ _ s => s.2 ^ 2 - s.1 * (1 - s.1))
    (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t b : ℝ), R.readout () () (t, b) ≤ 0 ↔ rightClaim t b

private theorem actual_bridge :
    (type_of% (@b_constraint_recenter)) ↔ arena.Law actual := by
  constructor
  · intro h t b
    have h' := h t b
    change (b ^ 2 - t * (1 - t) ≤ 0 ↔ rightClaim t b)
    constructor
    · intro hb
      exact h'.mp (by linarith)
    · intro hb
      have hleft := h'.mpr hb
      linarith
  · intro h t b
    have h' := h t b
    change (b ^ 2 ≤ t * (1 - t) ↔ rightClaim t b)
    change (b ^ 2 - t * (1 - t) ≤ 0 ↔ rightClaim t b) at h'
    constructor
    · intro hb
      exact h'.mp (by linarith)
    · intro hb
      have hleft := h'.mpr hb
      linarith

private theorem actual_law : arena.Law actual :=
  actual_bridge.mp (@b_constraint_recenter)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  change (1 : ℝ) ≤ 0 ↔ rightClaim 0 0 at hh
  norm_num [rightClaim] at hh

private theorem actual_dependence :
    ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), (0, 0), (0, 1), ?_⟩
  change ((0 : ℝ) ^ 2 - 0 * (1 - 0)) ≠ (1 : ℝ) ^ 2 - 0 * (1 - 0)
  norm_num

noncomputable def source : Registration arena (type_of% (@b_constraint_recenter)) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_law, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@b_constraint_recenter)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.OriginExclusionSegmentRigidity.b_constraint_recenter.__information_unit
  realizationName := `Reg.D5.S3.Quantum.OriginExclusionSegmentRigidity.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ s => s.2 ^ 2 - s.1 * (1 - s.1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source
#print axioms registration

end Reg.D5.S3.Quantum.OriginExclusionSegmentRigidity
