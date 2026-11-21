import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff
import Reg.Support.SingleDependentReadout

/-! Observational dependence and a rejected intervention for the Chebyshev root sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real
open LeanInformationAudit
open scoped ArithmeticFunction.Moebius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => theta t) (fun e => nomatch e)

def altered : Realization signature :=
  realize signature (fun _ _ t =>
    psi t + (∑ d ∈ Finset.Icc 2 2, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))) + 1000)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {t : ℝ}, 2 ≤ t → ∀ {m : ℕ}, 2 ≤ m →
    |V.readout () () t - psi t -
      ∑ d ∈ Finset.Icc 2 m, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))| ≤
      (log 4 + 4) * 2 * (1 + (m + 1 : ℝ) / log 2) * t ^ (1 / (m + 1 : ℝ))

private theorem actual_depends : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change theta 1 ≠ theta 2
  rw [theta_eq_zero_of_lt_two (by norm_num : (1 : ℝ) < 2)]
  exact ne_of_lt (theta_pos le_rfl)

private theorem alteration_rejected : ¬ arena.Law altered := by
  intro h
  have hp : (2 : ℝ) ^ (1 / ((2 : ℝ) + 1)) ≤ 2 :=
    rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hlog : (1 / 2 : ℝ) ≤ log 2 := by
    linarith [log_two_gt_d9]
  have hlog₄ : log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow, Nat.cast_ofNat]
    linarith [log_le_sub_one_of_pos (x := 2) (by norm_num)]
  have hdiv : (3 : ℝ) / log 2 ≤ 6 := by
    apply (div_le_iff₀ (by linarith : 0 < log 2)).mpr
    linarith
  have hbad := h (t := 2) (by norm_num) (m := 2) (by norm_num)
  dsimp [altered, realize] at hbad
  have hc (a b : ℝ) : a + b + 1000 - a - b = 1000 := by ring
  rw [hc, abs_of_pos (by norm_num : (0 : ℝ) < 1000)] at hbad
  have hmax :
      (log 4 + 4) * 2 * (1 + (2 + 1 : ℝ) / log 2) * (2 : ℝ) ^ (1 / (2 + 1 : ℝ)) ≤
        (6 : ℝ) * 2 * 7 * 2 := by
    gcongr <;> linarith only [hlog₄, hdiv]
  norm_num at hmax hbad
  linarith

def family : Registration arena (type_of% @chebyshev_mobius_truncation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chebyshev_mobius_truncation, altered, alteration_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual altered alteration_rejected
  dependence := actual_depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chebyshev_mobius_truncation) (Realization signature) Unit Unit where
  unitName := .str ``chebyshev_mobius_truncation "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => theta t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg",
        "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff
