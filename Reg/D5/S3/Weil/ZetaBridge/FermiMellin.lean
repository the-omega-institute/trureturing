import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.FermiMellin
import Reg.Support.SingleDependentReadout

/-! The Fermi factor readout in the exponential upper bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.FermiMellin

namespace Reg.D5.S3.Weil.ZetaBridge.FermiMellin

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : ℝ, R.readout () () t ≤ Real.exp (-t)

def actual : Realization signature :=
  realize signature (fun _ _ t => fermi t) (fun e => nomatch e)

private def excessive : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem excessive_rejected : ¬ arena.Law excessive := by
  intro h
  have hzero := h 0
  change (2 : ℝ) ≤ Real.exp (-(0 : ℝ)) at hzero
  norm_num at hzero

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change fermi 0 ≠ fermi 1
  apply ne_of_gt
  unfold fermi
  apply (inv_lt_inv₀ (by positivity) (by positivity)).2
  exact add_lt_add_right (Real.exp_lt_exp.mpr zero_lt_one) 1

def family : Registration arena (type_of% @fermi_le_exp_neg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fermi_le_exp_neg, excessive, excessive_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual excessive excessive_rejected
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fermi_le_exp_neg) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.FermiMellin.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => fermi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.FermiMellin
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaBridge.FermiMellin
