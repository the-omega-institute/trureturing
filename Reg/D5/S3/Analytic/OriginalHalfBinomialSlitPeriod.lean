import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
import Reg.Support.SingleDependentReadout

/-! Pointwise readout registrations for the positive period and complementary ratio. -/

open _root_.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod

noncomputable section

private theorem midpoint_mem : (1 / 2 : ℂ) ∈ doubleSlit := by
  constructor
  · change 1 - (1 / 2 : ℂ) ∈ Complex.slitPlane
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num))
  · exact Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num))

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

private def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def periodReadout : Realization signature :=
  realize signature (fun _ _ z => slitPeriod z) (fun e => nomatch e)

private def ratioReadout : Realization signature :=
  realize signature (fun _ _ z => tau z) (fun e => nomatch e)

private theorem period_dependence : ObservationalDependence signature periodReadout := by
  intro i
  by_contra h
  push Not at h
  have he : slitPeriod = fun _ : ℂ => slitPeriod 0 := by
    funext z
    exact h () z 0
  have hd : ∀ z, deriv slitPeriod z = 0 := by
    intro z
    conv_lhs => rw [he]
    simp
  have hw := slit_wronskian midpoint_mem
  norm_num [hd, Real.pi_ne_zero] at hw
  exact (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hw.symm

private theorem ratio_dependence : ObservationalDependence signature ratioReadout := by
  intro i
  by_contra h
  push Not at h
  have he : tau = fun _ : ℂ => tau 0 := by
    funext z
    exact h () z 0
  have hd : deriv tau (1 / 2 : ℂ) = 0 := by
    conv_lhs => rw [he]
    simp
  have hτ := (tau_hasDerivAt midpoint_mem).deriv
  have hp := slitPeriod_ne_zero midpoint_mem.1
  have hn : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hd] at hτ
  have hne : -Complex.I / ((Real.pi : ℂ) * (1 / 2) * (1 - 1 / 2) *
      slitPeriod (1 / 2) ^ 2) ≠ 0 := by
    apply div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn (by norm_num)) (by norm_num))
      (pow_ne_zero 2 hp)
  exact hne hτ.symm

namespace PositivePeriod

private def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℂ}, r ∈ slitDomain → 0 < (R.readout () () r).re

private theorem rejected_fails : ¬ arena.Law zeroReadout := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h midpoint_mem.1)

def family : Registration arena (type_of% @slitPeriod_re_pos) where
  actual := periodReadout
  bridge := Iff.rfl
  variation := ⟨@slitPeriod_re_pos, zeroReadout, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law periodReadout zeroReadout rejected_fails
  dependence := period_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@slitPeriod_re_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.PositivePeriod.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.PositivePeriod.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => slitPeriod z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositivePeriod

namespace PositiveRatio

private def arena : Arena where
  signature := signature
  Law R := ∀ {r : ℂ}, r ∈ doubleSlit → 0 < (R.readout () () r).im

private theorem rejected_fails : ¬ arena.Law zeroReadout := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h midpoint_mem)

def family : Registration arena (type_of% @tau_im_pos) where
  actual := ratioReadout
  bridge := Iff.rfl
  variation := ⟨@tau_im_pos, zeroReadout, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ratioReadout zeroReadout rejected_fails
  dependence := ratio_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tau_im_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.PositiveRatio.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.PositiveRatio.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => tau z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveRatio

end
end Reg.D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
