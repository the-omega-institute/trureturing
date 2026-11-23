import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletCompletionGamma
import Reg.Support.SingleDependentReadout

/-! Typed observations at the original mathematical statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Classical
open Complex Filter Topology
open _root_.D5.S3.CharacterSums.DirichletCompletionGamma
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.CharacterSums.DirichletCompletionGamma

namespace Norm
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.Gamma x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {z : ℂ} (hz : 0 < z.re), ‖Complex.Gamma z‖ ≤ M.readout () () z.re
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (z := 1) (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 3, ?_⟩
  norm_num [actual, realize, show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]
def family : Registration arena (type_of% @norm_Gamma_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @norm_Gamma_le,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_Gamma_le) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletionGamma.norm_Gamma_le
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletionGamma.Norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.Gamma x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletionGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Norm

namespace Convex
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => max x y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {u : ℝ} (hu : 1 / 4 ≤ u),
    Real.Gamma u ≤ M.readout () () (Real.Gamma (1 / 4)) (Nat.factorial (⌈u⌉₊ - 1) : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (u := 1) (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @Gamma_le_max_factorial) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @Gamma_le_max_factorial,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Gamma_le_max_factorial) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletionGamma.Gamma_le_max_factorial
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletionGamma.Convex.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => max x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletionGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Convex

namespace Exponential
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop)
    (fun _ => Prop → Prop)
def actual : Realization signature :=
  realize signature (fun _ _ x => fun y => x ∨ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {u : ℝ} (hu : 1 / 4 ≤ u),
    M.readout () () (Real.Gamma u ≤ Real.Gamma (1 / 4))
      (Real.Gamma u < Real.exp ((u + 1) * Real.log (u + 1)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (u := 1) (by norm_num)
  exact hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro h
  have hh := congrFun h False
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @Gamma_le_exp_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @Gamma_le_exp_bound,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Gamma_le_exp_bound) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletionGamma.Gamma_le_exp_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletionGamma.Exponential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fun y => x ∨ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletionGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Exponential

namespace RealFactor
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.Gamma x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {s : ℂ} (hs : 0 < s.re),
    ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * M.readout () () (s.re / 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (s := 2) (by norm_num)
  have hp : 0 < Real.pi ^ (-(2 : ℂ).re / 2) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  change ‖Complex.Gammaℝ 2‖ ≤ Real.pi ^ (-(2 : ℂ).re / 2) * (-1) at hh
  nlinarith [norm_nonneg (Complex.Gammaℝ 2)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 3, ?_⟩
  norm_num [actual, realize, show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]
def family : Registration arena (type_of% @norm_GammaReal_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize, decide_eq_true_eq] using @norm_GammaReal_le,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_GammaReal_le) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletionGamma.norm_GammaReal_le
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletionGamma.RealFactor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.Gamma x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletionGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RealFactor

namespace LogarithmicSeries
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := Summable (fun n : ℕ => M.readout () () (n : ℝ) / (n : ℝ) ^ 2) ∧
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ≤
      Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 ∧
    Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 < 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ 2 / (n : ℝ) ^ 2) := h.1
  have he : (fun n : ℕ => (n : ℝ) ^ 2 / (n : ℝ) ^ 2) =ᶠ[atTop]
      fun _ => (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_self (pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0)))
  have ht := hs.tendsto_atTop_zero.congr' he
  have hz : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at hz
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne
def family : Registration arena (type_of% @logarithmic_series_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize] using logarithmic_series_bound,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@logarithmic_series_bound) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletionGamma.logarithmic_series_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletionGamma.LogarithmicSeries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletionGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end LogarithmicSeries

namespace DigammaHeight
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law M := ∀ {z : ℂ} (hz : 1 ≤ z.re) (hz' : z.re ≤ 3 / 2),
    (Complex.digamma z).re ≤ M.readout () () (2 * |z.im| + 3) - Real.log 2 + 1 / 2 -
      (1 / (2 * z)).re
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (z := 1) (by norm_num) (by norm_num)
  norm_num [rejected, realize, Complex.digamma_one] at hh
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne
def family : Registration arena (type_of% @digamma_re_lt_log_height) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    simpa only [arena, actual, realize] using @digamma_re_lt_log_height,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@digamma_re_lt_log_height) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletCompletionGamma.digamma_re_lt_log_height
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCompletionGamma.DigammaHeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCompletionGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end DigammaHeight

end Reg.D5.S3.CharacterSums.DirichletCompletionGamma
