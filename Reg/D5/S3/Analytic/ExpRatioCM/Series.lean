import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExpRatioCM.Positive
import D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.ExpRatioCM.Series
open _root_.D5.S3.Analytic.ExpRatioCM.Positive
open LeanInformationAudit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Reg.D5.S3.Analytic.ExpRatioCM.Series

abbrev coefficientSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ i n => quotCoeff i n) (fun e => nomatch e)

def coefficientZero : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

def coefficientTwo : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem coefficientDependence : ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change quotCoeff 1 0 ≠ quotCoeff 1 1
  norm_num [quotCoeff, Finset.sum_range_succ]

namespace Second

def arena : Arena where
  signature := coefficientSignature
  Law R := ∀ i : ℕ, R.readout () i 2 = 2 * (3 : ℝ) ^ i - (4 : ℝ) ^ i

private theorem rejected : ¬ arena.Law coefficientZero := by
  intro h
  have h0 := h 0
  norm_num [coefficientZero, realize] at h0

def family : Registration arena (type_of% @quotCoeff_two) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨quotCoeff_two, coefficientZero, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law coefficientActual coefficientZero rejected
  dependence := coefficientDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quotCoeff_two) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.Second.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.Second.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ i n => quotCoeff i n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Second

namespace Bound

def arena : Arena where
  signature := coefficientSignature
  Law R := ∀ i n : ℕ, |R.readout () i n| ≤ ((2 : ℝ) ^ (i + 2)) ^ n

private theorem rejected : ¬ arena.Law coefficientTwo := by
  intro h
  have h0 := h 0 0
  norm_num [coefficientTwo, realize] at h0

def family : Registration arena (type_of% @abs_quotCoeff_le) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨abs_quotCoeff_le, coefficientTwo, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law coefficientActual coefficientTwo rejected
  dependence := coefficientDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@abs_quotCoeff_le) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.Bound.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.Bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ i n => quotCoeff i n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Bound
open _root_.D5.S3.Analytic.ExpRatioCM.Defs
open scoped Topology
open Set

abbrev momentSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def momentActual : Realization momentSignature :=
  realize momentSignature (fun _ i t => F i t) (fun e => nomatch e)
def secondActual : Realization momentSignature :=
  realize momentSignature (fun _ i t => G i t) (fun e => nomatch e)
def zeroMoment : Realization momentSignature :=
  realize momentSignature (fun _ _ _ => 0) (fun e => nomatch e)
def oneMoment : Realization momentSignature :=
  realize momentSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem momentDependence : ObservationalDependence momentSignature momentActual := by
  intro i
  refine ⟨0, 0, Real.log 2, ?_⟩
  change F 0 0 ≠ F 0 (Real.log 2)
  norm_num [F, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

private theorem secondDependence : ObservationalDependence momentSignature secondActual := by
  intro i
  refine ⟨0, 0, Real.log 2, ?_⟩
  change G 0 0 ≠ G 0 (Real.log 2)
  norm_num [G, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

namespace Composition
def arena : Arena where
  signature := momentSignature
  Law R := ∀ (i k : ℕ) (t : ℝ), iteratedDeriv k (R.readout () i) t = (-1) ^ k * F (i + k) t
private theorem rejected : ¬ arena.Law oneMoment := by
  intro h
  have hh := h 0 0 (Real.log 3)
  norm_num [oneMoment, realize, F, Real.exp_log (by norm_num : (0 : ℝ) < 3)] at hh
def family : Registration arena (type_of% (@iteratedDeriv_F)) where
  actual := momentActual
  bridge := Iff.rfl
  variation := ⟨@iteratedDeriv_F, oneMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law momentActual oneMoment rejected
  dependence := momentDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@iteratedDeriv_F) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.Composition.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.Composition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => F i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Composition

namespace MomentExpansion
def arena : Arena where
  signature := momentSignature
  Law R := ∀ (i : ℕ) {t : ℝ}, 0 < t → R.readout () i t = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ i * Real.exp (-((n + 1 : ℕ) : ℝ) * t)
private theorem rejected : ¬ arena.Law zeroMoment := by
  intro h
  have hh := h 0 (t := 1) (by norm_num)
  have hf := F_eq_tsum 0 (t := 1) (by norm_num)
  have hp := F_pos 0 (t := 1) (by norm_num)
  change 0 = _ at hh
  linarith
def family : Registration arena (type_of% (@F_eq_tsum)) where
  actual := momentActual
  bridge := Iff.rfl
  variation := ⟨@F_eq_tsum, zeroMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law momentActual zeroMoment rejected
  dependence := momentDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@F_eq_tsum) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.MomentExpansion.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.MomentExpansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => F i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end MomentExpansion

namespace MomentPositive
def arena : Arena where
  signature := momentSignature
  Law R := ∀ (i : ℕ) {t : ℝ}, 0 < t → 0 < R.readout () i t
private theorem rejected : ¬ arena.Law zeroMoment := by
  intro h
  have hh := h 0 (t := 1) (by norm_num)
  norm_num [zeroMoment, realize] at hh
def family : Registration arena (type_of% (@F_pos)) where
  actual := momentActual
  bridge := Iff.rfl
  variation := ⟨@F_pos, zeroMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law momentActual zeroMoment rejected
  dependence := momentDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@F_pos) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.MomentPositive.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.MomentPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => F i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end MomentPositive

namespace SecondPositiveOrder
def arena : Arena where
  signature := momentSignature
  Law R := ∀ {i : ℕ}, 1 ≤ i → ∀ {t : ℝ}, 0 < t → R.readout () i t = F i t
private theorem rejected : ¬ arena.Law zeroMoment := by
  intro h
  have hh := h (i := 1) (by omega) (t := 1) (by norm_num)
  have hp := F_pos 1 (t := 1) (by norm_num)
  change 0 = F 1 1 at hh
  linarith
def family : Registration arena (type_of% (@G_eq_F)) where
  actual := secondActual
  bridge := Iff.rfl
  variation := ⟨@G_eq_F, zeroMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law secondActual zeroMoment rejected
  dependence := secondDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@G_eq_F) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.SecondPositiveOrder.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.SecondPositiveOrder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => G i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end SecondPositiveOrder

def ratioActual : Realization momentSignature :=
  realize momentSignature (fun _ i t => ratioF i t) (fun e => nomatch e)
def secondRatioActual : Realization momentSignature :=
  realize momentSignature (fun _ i t => ratioG i t) (fun e => nomatch e)

private theorem ratioZero {t : ℝ} (ht : 0 < t) :
    ratioF 0 t = Real.exp t / (Real.exp t - 1) := by
  have hn : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  have he : deriv (fun x : ℝ => Real.log (1 - Real.exp (-x))) =ᶠ[𝓝 t] F 0 := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    simpa only [F, pow_zero, iteratedDeriv_zero, one_mul] using
      (D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives.log_one_sub_exp_derivatives.2 x hx).1
  have hd := (D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives.log_one_sub_exp_derivatives.2 t ht).2.1
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', he.iteratedDeriv_eq 1,
    iteratedDeriv_F] at hd
  norm_num only [zero_add, pow_one, neg_mul, one_mul] at hd
  rw [neg_div] at hd
  have hf := neg_injective hd
  change F 1 t / F 0 t = _
  rw [hf]
  simp only [F, pow_zero, iteratedDeriv_zero, one_mul]
  field_simp

private theorem ratioDependence : ObservationalDependence momentSignature ratioActual := by
  intro i
  refine ⟨0, Real.log 2, Real.log 3, ?_⟩
  change ratioF 0 (Real.log 2) ≠ ratioF 0 (Real.log 3)
  rw [ratioZero (Real.log_pos (by norm_num)), ratioZero (Real.log_pos (by norm_num))]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log (by norm_num : (0 : ℝ) < 3)]

private theorem secondRatioZero {t : ℝ} (ht : 0 < t) :
    ratioG 0 t = 1 / (Real.exp t - 1) := by
  rw [ratioG, G_eq_F (by omega : 1 ≤ 0 + 1) ht, G_zero_eq ht]
  have he := ratioZero ht
  have hf := F_pos 0 ht
  have h0 : F 0 t = 1 / (Real.exp t - 1) := by simp [F]
  have hn : Real.exp t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr ht))
  change F 1 t / F 0 t = _ at he
  have h1 := (div_eq_iff hf.ne').mp he
  rw [h1, h0]
  field_simp
  <;> ring

private theorem secondRatioDependence : ObservationalDependence momentSignature secondRatioActual := by
  intro i
  refine ⟨0, Real.log 2, Real.log 3, ?_⟩
  change ratioG 0 (Real.log 2) ≠ ratioG 0 (Real.log 3)
  rw [secondRatioZero (Real.log_pos (by norm_num)), secondRatioZero (Real.log_pos (by norm_num))]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log (by norm_num : (0 : ℝ) < 3)]

def shiftedRatio : Realization momentSignature :=
  realize momentSignature (fun _ i t => ratioF i t + 1) (fun e => nomatch e)
def tiltedRatio : Realization momentSignature :=
  realize momentSignature (fun _ i t => ratioF i t + t) (fun e => nomatch e)

namespace RatioAgreement
def arena : Arena where
  signature := momentSignature
  Law R := ∀ {i : ℕ}, 1 ≤ i → ∀ {t : ℝ}, 0 < t → R.readout () i t = ratioF i t
private theorem rejected : ¬ arena.Law zeroMoment := by
  intro h
  have hh := h (i := 1) (by omega) (t := 1) (by norm_num)
  have hp : 0 < ratioF 1 1 := div_pos (F_pos 2 (by norm_num)) (F_pos 1 (by norm_num))
  change 0 = ratioF 1 1 at hh
  linarith
def family : Registration arena (type_of% (@ratioG_eq_ratioF)) where
  actual := secondRatioActual
  bridge := Iff.rfl
  variation := ⟨@ratioG_eq_ratioF, zeroMoment, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law secondRatioActual zeroMoment rejected
  dependence := secondRatioDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ratioG_eq_ratioF) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.RatioAgreement.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.RatioAgreement.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => ratioG i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end RatioAgreement

namespace RatioExpansion
def arena : Arena where
  signature := momentSignature
  Law R := ∀ (i : ℕ) {t : ℝ}, Real.log ((2 : ℝ) ^ (i + 2)) < t → R.readout () i t = ∑' n : ℕ, quotCoeff i n * Real.exp (-(n : ℝ) * t)
private theorem rejected : ¬ arena.Law shiftedRatio := by
  intro h
  have hh := h 0 (t := Real.log 4 + 1) (by norm_num)
  have hh' := ratioF_eq_tsum 0 (t := Real.log 4 + 1) (by norm_num)
  change ratioF 0 (Real.log 4 + 1) + 1 = _ at hh
  linarith
def family : Registration arena (type_of% (@ratioF_eq_tsum)) where
  actual := ratioActual
  bridge := Iff.rfl
  variation := ⟨@ratioF_eq_tsum, shiftedRatio, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ratioActual shiftedRatio rejected
  dependence := ratioDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ratioF_eq_tsum) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.RatioExpansion.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.RatioExpansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end RatioExpansion

namespace RatioDerivative
def arena : Arena where
  signature := momentSignature
  Law R := ∀ (i k : ℕ), 1 ≤ k → ∀ {t : ℝ}, Real.log ((2 : ℝ) ^ (i + 2)) < t → (-1) ^ k * iteratedDeriv k (R.readout () i) t = ∑' n : ℕ, quotCoeff i n * (n : ℝ) ^ k * Real.exp (-(n : ℝ) * t)
private theorem rejected : ¬ arena.Law tiltedRatio := by
  intro h
  let t : ℝ := Real.log 4 + 1
  have ht : Real.log ((2 : ℝ) ^ (0 + 2)) < t := by dsimp [t]; norm_num
  have ht0 : 0 < t := by dsimp [t]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hh := h 0 1 (by omega) (t := t) ht
  have hh' := iteratedDeriv_ratioF 0 1 (by omega) ht
  have hd := ((contDiffOn_ratioF 0).differentiableOn (by simp) t ht0).differentiableAt (Ioi_mem_nhds ht0)
  change (-1 : ℝ) ^ 1 * iteratedDeriv 1 (fun x => ratioF 0 x + x) t = _ at hh
  simp only [iteratedDeriv_one, pow_one] at hh hh'
  have he : deriv (fun x => ratioF 0 x + x) t = deriv (ratioF 0) t + 1 := by
    convert (hd.hasDerivAt.add (hasDerivAt_id t)).deriv using 1
    congr 1
  rw [he] at hh
  linarith
def family : Registration arena (type_of% (@iteratedDeriv_ratioF)) where
  actual := ratioActual
  bridge := Iff.rfl
  variation := ⟨@iteratedDeriv_ratioF, tiltedRatio, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ratioActual tiltedRatio rejected
  dependence := ratioDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@iteratedDeriv_ratioF) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.RatioDerivative.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Series.RatioDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end RatioDerivative

end Reg.D5.S3.Analytic.ExpRatioCM.Series
