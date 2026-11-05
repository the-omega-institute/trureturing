import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathFeedbackRigidity
import Reg.Support.SingleDependentReadout

/-! Source-bound equality readout for the finite core of canonical proof atom
71554aa3b6c686d67a22ccc475f486cb7cb2ce48dad3074847c88544498c9516,
theorem `trace_saturation_forces_polar_feedback`. -/

open _root_.D5.S3.Quantum.Recovery.FourPathFeedbackRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FourPathFeedbackRigidity

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ), U ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ →
    (∀ i, v i ≠ 0) →
    ‖Matrix.trace (U * Matrix.diagonal v)‖ = ∑ i, ‖v i‖ →
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ i j,
      R.readout () () (U i j)
        (if i = j then z * star (v i) / (‖v i‖ : ℂ) else 0)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨z, hz, hh⟩ := h 0 1 (fun _ => 1) (by simp) (by simp)
    (by norm_num [Matrix.trace, Matrix.diag_apply])
  exact hh 0 0

def registration : Registration arena (type_of% trace_saturation_forces_polar_feedback) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_saturation_forces_polar_feedback, rejected, rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := by
    intro i
    refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
    intro h
    have hf : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
    norm_num at hf

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    trace_saturation_forces_polar_feedback (Realization signature) Type Unit where
  unitName := `D5.S3.Quantum.Recovery.FourPathFeedbackRigidity.trace_saturation_forces_polar_feedback.audit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathFeedbackRigidity.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.FourPathFeedbackRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.FourPathFeedbackRigidity
