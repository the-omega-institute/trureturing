import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapReplay
import Reg.Support.SingleDependentReadout

/-! Register the mixed-derivative sign for lower coordinate at least four. -/

noncomputable section

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapReplay

open _root_.RefinedBMV.PositiveCenter
open _root_.RefinedBMV.PositiveCenter.MiddleGapReplay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ v f => deriv f v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, 11 ≤ p → ∀ {u v : ℝ}, 4 ≤ u → u < v →
    R.readout () v (fun y ↦ deriv (fun x ↦ logKernel p x y) u) < 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (lt_irrefl (0 : ℝ))
    (h (p := 11) (by decide) (u := 4) (v := 5)
      (by norm_num) (by norm_num))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun t => t), ?_⟩
  change deriv (fun _ : ℝ => (0 : ℝ)) 0 ≠ deriv (fun t : ℝ => t) 0
  simp [deriv_id'']

def source_registration : Registration arena (type_of% @logKernel_mixed_of_lower_four_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logKernel_mixed_of_lower_four_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@logKernel_mixed_of_lower_four_le) (Realization signature) Type Unit where
  unitName := `RefinedBMV.PositiveCenter.MiddleGapReplay.logKernel_mixed_of_lower_four_le.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapReplay.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ v f => deriv f v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapReplay
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapReplay
