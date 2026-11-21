import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

/-- The varying root normalization in the integrated limit. -/
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def zeroScale : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    Tendsto (fun x => V.readout () () x * (Q x - primeTail x)) atTop (𝓝 2) ∧
    ∀ C : ℝ, (∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * Real.sqrt t) →
      (∀ x, 1 ≤ x → 0 ≤ Q x - primeTail x ∧ Q x - primeTail x ≤ 2 * C / Real.sqrt x) ∧
      ∀ a b : ℝ, 1 ≤ a → a ≤ b →
        let W := ∫ x in a..b, (max (-primeTail x) 0 - max (-Q x) 0) / Real.sqrt x
        0 ≤ W ∧ W ≤ 2 * C * Real.log (b / a)

private theorem zeroScale_fails : ¬ arena.Law zeroScale := by
  intro h
  have ht := h.1
  change Tendsto (fun x => (0 : ℝ) * (Q x - primeTail x)) atTop (𝓝 2) at ht
  simp only [zero_mul] at ht
  have he : (0 : ℝ) = 2 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change Real.sqrt 0 ≠ Real.sqrt 1
  norm_num

def family : Registration arena (type_of% @prime_power_window_correction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_power_window_correction, zeroScale, zeroScale_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroScale zeroScale_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_power_window_correction) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection.prime_power_window_correction
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem primeTail_two_le : primeTail 2 ≤ -1 / 4 := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have horder := ((prime_power_window_correction.2 C (fun t _ => hC t)).1 2 (by norm_num)).1
  have hQ := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable
    (t := 2) le_rfl
  change Q 2 = _ at hQ
  have hfloor : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  have hsmall : Finset.Ioc (0 : ℕ) 2 = {1, 2} := by decide
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he := Real.one_half_lt_eulerMascheroniConstant
  simp [Chebyshev.psi, hfloor, hsmall, ArithmeticFunction.vonMangoldt_apply_one] at hQ
  linarith

abbrev windowLowerArena : Arena where
  signature := signature
  Law V :=
    ∀ {a b x r : ℝ}, 1 ≤ a → a ≤ (1 - r) * x → (1 + r) * x ≤ b →
      0 < r → r ≤ 1 / 2 → primeTail x ≤ -4 * r ^ 2 →
      r ^ 3 * Real.sqrt x ≤ ∫ z in a..b, max (-primeTail z) 0 / V.readout () () z

private theorem zeroScale_fails_window_lower : ¬ windowLowerArena.Law zeroScale := by
  intro h
  have hp := h (a := 1) (b := 3) (x := 2) (r := 1 / 4)
    le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (primeTail_two_le.trans_eq (by norm_num))
  change (1 / 4 : ℝ) ^ 3 * Real.sqrt 2 ≤
    ∫ z in (1 : ℝ)..3, max (-primeTail z) 0 / 0 at hp
  simp only [div_zero, intervalIntegral.integral_zero] at hp
  exact (not_le_of_gt (by positivity :
    0 < (1 / 4 : ℝ) ^ 3 * Real.sqrt 2)) hp

def windowLowerFamily : Registration windowLowerArena (type_of% @prime_tail_negative_window_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_tail_negative_window_lower, zeroScale, zeroScale_fails_window_lower⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    windowLowerArena.Law actual zeroScale zeroScale_fails_window_lower
  dependence := actual_dependence

noncomputable def windowLowerAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_tail_negative_window_lower) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection.prime_tail_negative_window_lower
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection "windowLowerFamily"
  realizationSource := none
  generated := false
  arena := .source ⟨windowLowerArena⟩
  objectArena := .source ⟨windowLowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowLowerArena ⟨windowLowerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "fn", "arg", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
