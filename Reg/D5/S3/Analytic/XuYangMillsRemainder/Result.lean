import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.XuYangMillsRemainder.Result
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.Analytic.XuYangMillsRemainder.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set Real MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n →
    CompletelyMonotoneOn (fun x => (-1:ℝ)^n * D n (R.readout () () x) (-1))

private theorem mills_neg_one_pos : 0 < millsRatio (-1) := by
  have hi : IntegrableOn (fun t : ℝ => exp (-t^2/2)) (Ioi (-1)) := by
    convert (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).integrableOn
      (s := Ioi (-1)) using 1
    ext t
    congr 1
    ring
  have : NeZero (volume (Ioi (-1:ℝ))) := ⟨by simp⟩
  unfold millsRatio
  exact mul_pos (exp_pos _) (integral_exp_pos hi)

private theorem small_coefficients :
    u 1 (-1) (-3) = 0 ∧ u 2 (-1) (-3) = 0 ∧ u 3 (-1) (-3) = -2 := by
  have hg1 : Gamma ((1:ℝ)+1/2) = (1/2)*Gamma (1/2) := by
    rw [show (1:ℝ)+1/2 = (1/2)+1 by ring, Gamma_add_one (by norm_num)]
  have hg2 : Gamma ((2:ℝ)+1/2) = (3/2)*((1/2)*Gamma (1/2)) := by
    rw [show (2:ℝ)+1/2 = ((1:ℝ)+1/2)+1 by ring, Gamma_add_one (by norm_num), hg1]
    ring
  have hg3 : Gamma ((3:ℝ)+1/2) = (5/2)*((3/2)*((1/2)*Gamma (1/2))) := by
    rw [show (3:ℝ)+1/2 = ((2:ℝ)+1/2)+1 by ring, Gamma_add_one (by norm_num), hg2]
    ring
  norm_num at hg1 hg2 hg3
  have hz : Gamma ((2:ℝ)⁻¹) ≠ 0 := ne_of_gt (Gamma_pos_of_pos (by positivity))
  constructor
  · norm_num [u, Finset.sum_range_succ, hg1, hg2, hg3]
    field_simp
    ring
  · constructor
    · norm_num [u, Finset.sum_range_succ, hg1, hg2, hg3]
      field_simp
      ring
    · norm_num [u, Finset.sum_range_succ, hg1, hg2, hg3]
      field_simp
      ring

private theorem D_three_neg_one : D 3 (-1) (-1) = 3*millsRatio (-1) := by
  have hu := small_coefficients
  norm_num [D, Y, show Finset.Icc 1 3 = {1,2,3} by decide, hu.1, hu.2.1, hu.2.2]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 3 (by norm_num)).2 0 1 (by norm_num)
  change 0 ≤ (-1:ℝ)^0 * iteratedDeriv 0
    (fun _ : ℝ => (-1:ℝ)^3 * D 3 (-1) (-1)) 1 at h0
  norm_num only [iteratedDeriv_zero, pow_zero, one_mul, pow_succ] at h0
  rw [D_three_neg_one] at h0
  nlinarith [mills_neg_one_pos]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Analytic.XuYangMillsRemainder.Result.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := some {
      owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
      name := `D5.S3.Analytic.XuYangMillsRemainder.Result.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace PolynomialRecurrence

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ m => intPow m) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, (2 * (m : ℝ) + 3) * intPow (m + 1) -
    2 * (m + 1) * R.readout () () m = 2 ^ (m + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 0
  have H0 := intPow_rec 0
  have hi0 : intPow 0 = 1 := by norm_num [intPow]
  norm_num [rejected, realize] at H
  norm_num [hi0] at H0
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change intPow 0 ≠ intPow 1
  have h0 : intPow 0 = 1 := by norm_num [intPow]
  have h1 := intPow_rec 0
  norm_num at h1
  intro he
  rw [← he, h0] at h1
  norm_num at h1

def family : Registration arena (type_of% @intPow_rec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intPow_rec, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@intPow_rec) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.PolynomialRecurrence.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.PolynomialRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => intPow m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolynomialRecurrence

namespace CoefficientSum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ m => intPow m) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, (∑ j ∈ Finset.range (m + 1), coeff j / j.factorial) =
    coeff (m + 1) / ((2 : ℝ) ^ m * m.factorial) * R.readout () () m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 0
  have hc1 := coeff_factorial 0
  norm_num at hc1
  have hc := coeff_sum 0
  norm_num [intPow, hc1] at hc
  norm_num [rejected, realize, hc] at H

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change intPow 0 ≠ intPow 1
  have h0 : intPow 0 = 1 := by norm_num [intPow]
  have h1 := intPow_rec 0
  norm_num at h1
  intro he
  rw [← he, h0] at h1
  norm_num at h1

def family : Registration arena (type_of% @coeff_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coeff_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coeff_sum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.CoefficientSum.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.CoefficientSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => intPow m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoefficientSum

namespace CoefficientFactorial

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ m => coeff (m + 1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, R.readout () () m * ((2 : ℝ) ^ m * m.factorial) =
    (2 * m + 1).factorial

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 0
  norm_num [rejected, realize] at H

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change coeff (0 + 1) ≠ coeff (1 + 1)
  have h0 := coeff_factorial 0
  have h1 := coeff_factorial 1
  norm_num at h0 h1 ⊢
  linarith

def family : Registration arena (type_of% @coeff_factorial) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coeff_factorial, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coeff_factorial) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.CoefficientFactorial.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.CoefficientFactorial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => coeff (m + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoefficientFactorial

namespace ExponentialRemainderIdentity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ r v => expRemainder r v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, ∀ v : ℝ, R.readout () r v = (-1:ℝ)^r *
    (exp (-v) - ∑ j ∈ Finset.range r, (-v)^j / j.factorial)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 0 0
  norm_num [rejected, realize] at H

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change expRemainder 0 0 ≠ expRemainder 0 1
  simp only [expRemainder_eq]
  have he : exp (-1 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
  norm_num <;> linarith

def family : Registration arena (type_of% @expRemainder_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@expRemainder_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@expRemainder_eq) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.ExponentialRemainderIdentity.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.ExponentialRemainderIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => expRemainder r v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExponentialRemainderIdentity

namespace ExponentialRemainderBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ r v => expRemainder r v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, ∀ {v : ℝ}, 0 ≤ v →
    0 ≤ R.readout () r v ∧ expRemainder r v ≤ v^r / r.factorial

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := (h 0 (v := 0) (by norm_num)).1
  norm_num [rejected, realize] at H

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change expRemainder 0 0 ≠ expRemainder 0 1
  simp only [expRemainder_eq]
  have he : exp (-1 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
  norm_num <;> linarith

def family : Registration arena (type_of% @expRemainderBounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@expRemainderBounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@expRemainderBounds) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.ExponentialRemainderBound.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.ExponentialRemainderBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => expRemainder r v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExponentialRemainderBound

namespace ExponentialRemainderRecurrence

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ r v => expRemainder (r+1) v) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ r : ℕ, ∀ v : ℝ, R.readout () r v =
    v^r / r.factorial - expRemainder r v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h 0 0
  norm_num [rejected, realize, expRemainder_eq] at H

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change expRemainder 1 0 ≠ expRemainder 1 1
  simp only [expRemainder_eq]
  have he : exp (-1 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
  norm_num <;> linarith

def family : Registration arena (type_of% @expRemainderRec) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@expRemainderRec, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@expRemainderRec) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.ExponentialRemainderRecurrence.unit
  realizationName := `Reg.D5.S3.Analytic.XuYangMillsRemainder.Result.ExponentialRemainderRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r v => expRemainder (r+1) v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.XuYangMillsRemainder.Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExponentialRemainderRecurrence

end
end Reg.D5.S3.Analytic.XuYangMillsRemainder.Result
