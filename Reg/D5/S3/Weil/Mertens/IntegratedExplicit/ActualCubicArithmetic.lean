import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic
import Reg.Support.SingleDependentReadout

/-! The endpoint weight is the readout in the normalized arithmetic lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Real Set LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (Q psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (r weightedTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent (W R)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
  (actualCompleteSpectrum)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
  (lowHeight cubicLowMass quadraticHighMass)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ b => W b) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law O := ∀ {b T : ℝ}, log 2 ≤ b → 0 < T →
    (∀ k : ℕ, |(actualZero k).im| ≤ T → (actualZero k).re = 1 / 2) →
    -(O.readout () () b / R b) * (exp (-b / 2) * cubicLowMass T + quadraticHighMass T / T) -
        log (2 * Real.pi) * exp (-b) / (b + 1) ≤
      Q (exp b) - weightedTail psiErrorKernel (exp b) / r (exp b)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize, W]

private def constantReadout (w : ℝ) : Realization signature :=
  realize signature (fun _ _ _ => w) (fun e => nomatch e)

private theorem exists_rejected : ∃ w : ℝ, ¬ arena.Law (constantReadout w) := by
  have hnone (k : ℕ) : ¬ |(actualZero k).im| ≤ 1 := by
    have hgt : 10 < |(actualZero k).im| := actualCompleteSpectrum.height k
    linarith
  have hsum : Summable (fun k : ℕ => 1 / |(actualZero k).im| ^ 2) := by
    simpa only [Function.comp_def, actualZero, sq_abs, one_div, inv_pow] using
      (actualOccurrenceEquiv.summable_iff).2 actual_sigma_inverse_square_summable
  let k : ((lowHeight 1)ᶜ : Set ℕ) := ⟨0, hnone 0⟩
  have hk : 0 < |(actualZero (k : ℕ)).im| :=
    (by norm_num : (0 : ℝ) < 10).trans (actualCompleteSpectrum.height k)
  have hhigh : 0 < quadraticHighMass 1 :=
    (hsum.subtype ((lowHeight 1)ᶜ : Set ℕ)).tsum_pos
      (fun i => show 0 ≤ 1 / |(actualZero i.val).im| ^ 2 by positivity) k
      (show 0 < 1 / |(actualZero (k : ℕ)).im| ^ 2 by positivity)
  have hlow : 0 ≤ cubicLowMass 1 := tsum_nonneg (fun _ => by positivity)

  let m := exp (-(1 : ℝ) / 2) * cubicLowMass 1 + quadraticHighMass 1 / 1
  have hm : 0 < m := add_pos_of_nonneg_of_pos
    (mul_nonneg (exp_nonneg _) hlow) (div_pos hhigh one_pos)
  let c := log (2 * Real.pi) * exp (-(1 : ℝ)) / (1 + 1)
  let q := Q (exp 1) - weightedTail psiErrorKernel (exp 1) / r (exp 1)
  let w := -(q + c + 1) * R 1 / m
  refine ⟨w, ?_⟩
  intro h
  have hb : log (2 : ℝ) ≤ 1 := by
    have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog
    exact hlog
  have htest := h (b := 1) (T := 1) hb one_pos fun j hj => (hnone j hj).elim
  change -(w / R 1) * m - c ≤ q at htest
  have hR : R 1 ≠ 0 := by norm_num [R]
  have hw : -(w / R 1) * m - c = q + 1 := by
    dsimp only [w]
    field_simp [hm.ne', hR]
    <;> ring
  rw [hw] at htest
  linarith

def rejected : Realization signature := constantReadout (Classical.choose exists_rejected)

def evidence : Registration arena (type_of% @actual_cubic_arithmetic_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_cubic_arithmetic_lower_bound, rejected,
    Classical.choose_spec exists_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected (Classical.choose_spec exists_rejected)
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_cubic_arithmetic_lower_bound) (Realization signature) Unit Unit where
  unitName :=
    .str
      `D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic.actual_cubic_arithmetic_lower_bound
      "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => W b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicArithmetic
