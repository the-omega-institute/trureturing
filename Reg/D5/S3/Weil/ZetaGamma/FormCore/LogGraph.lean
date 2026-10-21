import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.LogGraph
import Reg.Support.SingleDependentReadout

/-! A source-bound audit of the logarithmic weight comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.LogGraph

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaGamma.FormCore.LogGraph
open LeanInformationAudit

abbrev weightSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ t => ell t) (fun e => nomatch e)

def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 2 * Real.log 3 + 2) (fun e => nomatch e)

def weightArena : Arena where
  signature := weightSignature
  Law R := ∀ t : ℝ,
    R.readout () () t ≤ Real.log 3 * (1 + Real.log (1 + |t|)) ∧
      (1 + Real.log (1 + |t|)) ≤ 2 * ell t

private theorem rejected_law : ¬ weightArena.Law weightRejected := by
  intro h
  have hzero := (h 0).1
  norm_num [weightRejected, realize] at hzero
  have hlog : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  linarith

def weightFamily : Registration weightArena (type_of% (@log_weight_dictionary)) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨log_weight_dictionary, weightRejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    weightArena.Law weightActual weightRejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change ell 0 ≠ ell 1
    have h : Real.log (3 : ℝ) < Real.log 4 :=
      Real.log_lt_log (by norm_num) (by norm_num)
    simpa [ell, show (1 : ℝ) + 3 = 4 by norm_num] using ne_of_lt h

def registration_log_weight_dictionary :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@log_weight_dictionary) (type_of% weightActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.LogGraph.log_weight_dictionary.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.LogGraph.weightFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ t => ell t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.LogGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Weil.ZetaGamma.FormCore.LogGraph
