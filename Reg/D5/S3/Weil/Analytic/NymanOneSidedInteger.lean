import D5.S3.Weil.Analytic.NymanOneSidedInteger
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Selection of the logarithmic signal in the transferred bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.Analytic.NymanOneSidedInteger

open _root_.NymanOneSidedScalar _root_.NymanOneSidedInteger _root_.NymanShellMellin
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped ArithmeticFunction.Moebius
open private scaled_finite from D5.S3.Weil.Analytic.NymanShellScale

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ W t => signal W t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {W : ℝ → ℝ}, (∀ x ∉ Set.Ioo (1 : ℝ) 2, W x = 0) →
    ∀ {K : ℝ}, 0 ≤ K → (∀ x y : ℝ, |W x - W y| ≤ K * |x - y|) →
    ∀ {β c C : ℝ}, 0 ≤ β → 0 ≤ C →
    (∀ N : ℕ, 0 < N → c * integerSample W N ≤ C * (N : ℝ) ^ β) →
    ∀ᶠ t in atTop, c * R.readout () W t ≤ (C + 10 * |c| * K) * Real.exp (β * t)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hf := h (W := fun _ => 0) (by simp) (K := 0) le_rfl (by simp)
    (β := 0) (c := 1) (C := 0) le_rfl le_rfl (by simp [integerSample, Wcomplex, scaled])
  simpa [rejected, realize] using hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  let W : ℝ → ℝ := fun x => if x = 3 / 2 then 1 else 0
  have hW : ∀ x ∉ Set.Ioo (1 : ℝ) 2, Wcomplex W x = 0 := by
    intro x hx
    have hne : x ≠ 3 / 2 := by
      rintro rfl
      exact hx ⟨by norm_num, by norm_num⟩
    simp [Wcomplex, W, hne]
  have hv (x : ℝ) (hx : 1 < x) :
      (scaled (Wcomplex W) x).re = W x := by
    rw [scaled_finite hW (by linarith) (R := 2) (by norm_num; linarith)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have hoff : Wcomplex W ((2 : ℝ) * x) = 0 := hW _ (by
      intro hm
      linarith [hm.2])
    simp [hoff, Wcomplex]
  refine ⟨W, 0, -Real.log (3 / 4), ?_⟩
  change signal W 0 ≠ signal W (-Real.log (3 / 4))
  unfold signal
  rw [neg_zero, Real.exp_zero, mul_one, neg_neg, Real.exp_log (by norm_num),
    hv 2 (by norm_num), hv (2 * (3 / 4)) (by norm_num)]
  norm_num [W]

def family : Registration arena (type_of% @one_sided_signal_of_integer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_sided_signal_of_integer, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@one_sided_signal_of_integer) (Realization signature) Unit Unit where
  unitName := `NymanOneSidedInteger.one_sided_signal_of_integer.__information_unit
  realizationName := `Reg.D5.S3.Weil.Analytic.NymanOneSidedInteger.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ W t => signal W t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Analytic.NymanOneSidedInteger
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Weil.Analytic.NymanOneSidedInteger
