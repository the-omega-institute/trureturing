import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ κ r => fun a =>
    normalizedLocalFactor κ r a ≥
      (1 - r) ^ (-κ) * (1 - r ^ κ) *
        (1 - localFactorConstant κ * r ^ (a + 1))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ r a : ℝ}, 1 ≤ κ → 0 ≤ r → r ≤ 1 / 2 → 1 ≤ a →
    R.readout () κ r a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (κ := 1) (r := 0) (a := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa [arena, rejected, realize] using hh

def family : Registration arena (type_of% @local_factor_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using @local_factor_lower_bound,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 0, -1, ?_⟩
    intro h
    have hp := @local_factor_lower_bound 2 0 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    have hleft : actual.readout i 2 0 1 := by
      simpa [actual, realize] using hp
    have hright : actual.readout i 2 (-1) 1 := by
      rw [← congrFun h 1]
      exact hleft
    have hbad : ¬ actual.readout i 2 (-1) 1 := by
      norm_num [actual, realize, normalizedLocalFactor, localFactorConstant]
    exact hbad hright

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@local_factor_lower_bound) (Realization signature) Type Unit where
  unitName := `LcmPowerLocalFactorBound.local_factor_lower_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ κ r => fun a =>
    normalizedLocalFactor κ r a ≥
      (1 - r) ^ (-κ) * (1 - r ^ κ) *
        (1 - localFactorConstant κ * r ^ (a + 1))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound
