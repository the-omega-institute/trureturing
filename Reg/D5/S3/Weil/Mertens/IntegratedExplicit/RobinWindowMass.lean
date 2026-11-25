import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
import Reg.D5.S3.Weil.Mertens.WeightedTailWindowMass

/-! The prime-only tail observed through the negative mass on the inner window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter LeanInformationAudit MeasureTheory Real Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
open _root_.Reg.D5.S3.Weil.Mertens.WeightedTailWindowMass (negative_sqrt_mass)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => primeTail) (fun e => nomatch e)

private def exaggeratedTail (bound : ℝ) (x : ℝ) : ℝ := -(max bound 0 + 1) * sqrt x

private lemma exaggerated_mass {bound Y X : ℝ} (hY : 0 < Y) (hwidth : 1 ≤ X - Y) :
    bound < ∫ x in Y..X, max (-exaggeratedTail bound x) 0 / sqrt x := by
  have hK : 0 ≤ max bound 0 + 1 := by linarith [le_max_right bound 0]
  change bound < ∫ x in Y..X, max (-(-(max bound 0 + 1) * sqrt x)) 0 / sqrt x
  rw [negative_sqrt_mass hY (by linarith) hK]
  have hscale := mul_le_mul_of_nonneg_right hwidth hK
  rw [one_mul] at hscale
  linarith [le_max_left bound 0]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let x : ℝ := 3 / 2
  refine ⟨(), 1, x, ?_⟩
  change primeTail 1 ≠ primeTail x
  intro h
  have hx₁ : 1 ≤ x := by norm_num [x]
  have hx₂ : x < 2 := by norm_num [x]
  let f (t : ℝ) := (Chebyshev.theta t - t) / t ^ 2
  have hzero : (∫ t in (1 : ℝ)..x, f t) = 0 := by
    change (∫ t in Ioi (1 : ℝ), f t) = ∫ t in Ioi x, f t at h
    rw [← intervalIntegral.integral_Ioi_sub_Ioi prime_integrable hx₁, h, sub_self]
  have hbound : (∫ t in (1 : ℝ)..x, f t) ≤ ∫ _ in (1 : ℝ)..x, -(1 / 2 : ℝ) := by
    apply intervalIntegral.integral_mono_on hx₁
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx₁).2
        (prime_integrable.mono_set Ioc_subset_Ioi_self)) intervalIntegrable_const
    intro t ht
    have ht₂ := ht.2.trans_lt hx₂
    have ht₀ : 0 < t := zero_lt_one.trans_le ht.1
    change (Chebyshev.theta t - t) / t ^ 2 ≤ -(1 / 2 : ℝ)
    rw [Chebyshev.theta_eq_zero_of_lt_two ht₂, zero_sub]
    apply (div_le_iff₀ (sq_pos_of_pos ht₀)).2
    nlinarith only [mul_pos ht₀ (sub_pos.mpr ht₂)]
  rw [hzero, intervalIntegral.integral_const] at hbound
  norm_num [x] at hbound

def intervalArena : Arena where
  signature := signature
  Law R := ∀ {C Y X B : ℝ} (_ : 2 ≤ Y) (_ : Y ≤ X) (_ : X ≤ B)
    (_ : ∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * sqrt t),
    (∫ x in Y..X, max (-R.readout () () x) 0 / sqrt x) ≤
      massFactor Y * weightedNegativeMass psiErrorKernel Y B +
        2 * (sqrt X - sqrt Y) * max (-endpointDefect psiErrorKernel B) 0 +
        2 * C * log (X / Y)

def powerArena : Arena where
  signature := signature
  Law R := ∀ {C Y d b : ℝ} (_ : exp 1 ≤ Y) (_ : 1 ≤ d) (_ : d ≤ b)
    (_ : ∀ t, 1 ≤ t → Chebyshev.psi t - Chebyshev.theta t ≤ C * sqrt t),
    (∫ x in Y..Y ^ d, max (-R.readout () () x) 0 / sqrt x) ≤
      4 * Y ^ ((d - 1) / 2) * robinBudget Y b + 2 * C * (d - 1) * log Y

private lemma interval_rejected :
    ∃ R : Realization signature, ¬ intervalArena.Law R := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let bound := massFactor 2 * weightedNegativeMass psiErrorKernel 2 3 +
    2 * (sqrt 3 - sqrt 2) * max (-endpointDefect psiErrorKernel 3) 0 + 2 * C * log (3 / 2)
  refine ⟨realize signature (fun _ _ => exaggeratedTail bound) (fun e => nomatch e), ?_⟩
  intro law
  have h := law (Y := 2) (X := 3) (B := 3) le_rfl (by norm_num) le_rfl (fun t _ => hC t)
  exact (exaggerated_mass (bound := bound) (Y := 2) (X := 3) (by norm_num) (by norm_num)).not_ge h

private lemma power_rejected :
    ∃ R : Realization signature, ¬ powerArena.Law R := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let Y := exp 1 + 2
  let bound := 4 * Y ^ (((2 : ℝ) - 1) / 2) * robinBudget Y 2 + 2 * C * (2 - 1) * log Y
  refine ⟨realize signature (fun _ _ => exaggeratedTail bound) (fun e => nomatch e), ?_⟩
  intro law
  have hY : exp 1 ≤ Y := by dsimp [Y]; linarith
  have hY₂ : 2 ≤ Y := by dsimp [Y]; linarith [exp_pos 1]
  have hwidth : 1 ≤ Y ^ (2 : ℝ) - Y := by
    rw [Real.rpow_two]
    nlinarith only [hY₂, mul_nonneg (sub_nonneg.mpr hY₂) (show 0 ≤ Y by linarith)]
  have h := law (Y := Y) (d := 2) (b := 2) hY (by norm_num) le_rfl (fun t _ => hC t)
  exact (exaggerated_mass (bound := bound) (by linarith) hwidth).not_ge h

def intervalEvidence : Registration intervalArena (type_of% @prime_mass_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_mass_le, Classical.choose interval_rejected,
    Classical.choose_spec interval_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    intervalArena.Law actual (Classical.choose interval_rejected)
    (Classical.choose_spec interval_rejected)
  dependence := actual_dependence

def powerEvidence : Registration powerArena (type_of% @prime_mass_le_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_mass_le_power, Classical.choose power_rejected,
    Classical.choose_spec power_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    powerArena.Law actual (Classical.choose power_rejected)
    (Classical.choose_spec power_rejected)
  dependence := actual_dependence

def intervalAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_mass_le) (Realization signature) Unit Unit where
  unitName := .str ``prime_mass_le "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass.intervalEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨intervalArena⟩
  objectArena := .source ⟨intervalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source intervalArena ⟨intervalEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => primeTail) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms intervalAudit

def powerAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_mass_le_power) (Realization signature) Unit Unit where
  unitName := .str ``prime_mass_le_power "__information_unit"
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass.powerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨powerArena⟩
  objectArena := .source ⟨powerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source powerArena ⟨powerEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => primeTail) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms powerAudit

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.RobinWindowMass
