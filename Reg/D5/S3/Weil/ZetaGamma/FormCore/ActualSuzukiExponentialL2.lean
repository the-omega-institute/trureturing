import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteMeanZeroWitness
import Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiWeightedPhysicalMoments
import Reg.Support.SingleDependentReadout

/-! Faithful source audits of exponential conjugation and the actual H6 budgets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
open _root_.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2

open private l1_exp_profile l1_exp_tail from
  D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass
open private thetaModeCoefficient thetaModeCoefficient_summable from
  D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiThetaExcess
open private indicatorInput indicator_h6 indicator_excess_pos indicator_excess_integrable from
  Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiWeightedPhysicalMoments

private theorem zero_h6 : originalPhysicalH6 (fun _ : ℝ => (0 : ℂ)) :=
  ⟨MemLp.zero', by simp⟩

private theorem zero_profile : actualGammaProfile (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
  funext t
  simp [actualGammaProfile, fullTheta, physicalTerm]

private theorem zero_even_b :
    actualSuzukiEvenBProfile (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
  funext r
  simp [actualSuzukiEvenBProfile, actualSuzukiBProfile, zero_profile, rightExponentialTail]

namespace ExponentialConjugation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ((_ : ℝ) × (ℝ → ℂ)) (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p t => rightExponentialTail p.1 p.2 t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (k a : ℝ) (u : ℝ → ℂ) (t : ℝ),
    (Real.exp (a * t) : ℂ) * R.readout () ⟨k, u⟩ t =
      rightExponentialTail (k + a) (fun x => (Real.exp (a * x) : ℂ) * u x) t

private theorem source_reconstruction :
    (type_of% (@right_exponential_tail_exponential_conjugation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall 0 0 (fun _ : ℝ => (0 : ℂ)) 0
  norm_num [rejected, realize, rightExponentialTail] at h

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, l1_exp_profile 1⟩, 0, 1, ?_⟩
  change rightExponentialTail 1 (l1_exp_profile 1) 0 ≠
    rightExponentialTail 1 (l1_exp_profile 1) 1
  rw [l1_exp_tail (by norm_num) (by norm_num),
    l1_exp_tail (by norm_num) (by norm_num)]
  intro heq
  have hre := congrArg Complex.re heq
  simp only [l1_exp_profile, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hre
  norm_num only [neg_mul, one_mul, mul_zero, neg_zero, Real.exp_zero,
    zero_mul, one_add_one_eq_two, inv_eq_one_div] at hre
  have hexp : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

def familyRegistration : Registration arena (type_of% (@right_exponential_tail_exponential_conjugation)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@right_exponential_tail_exponential_conjugation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_exponential_tail_exponential_conjugation) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2.ExponentialConjugation.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2.ExponentialConjugation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => rightExponentialTail p.1 p.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ExponentialConjugation

namespace GammaCriticalMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ F =>
    ∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℂ) (_hF : originalPhysicalH6 F),
    MemLp (fun t : ℝ => (Real.exp ((5 / 4 : ℝ) * t) : ℂ) *
        actualGammaProfile F t) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t : ℝ in Ioi 0,
        ‖(Real.exp ((5 / 4 : ℝ) * t) : ℂ) * actualGammaProfile F t‖ ^ 2) =
        Real.pi ^ (-(5 / 2 : ℝ)) * R.readout () () F

private theorem source_reconstruction :
    (type_of% (@actual_h6_gamma_profile_critical_exponential_l2_and_mass)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := (hall (fun _ : ℝ => (0 : ℂ)) zero_h6).2
  have hp : 0 < Real.pi ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos Real.pi_pos _
  simp only [rejected, realize, zero_profile, mul_zero, norm_zero, zero_pow,
    OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, integral_zero] at h
  change (0 : ℝ) = Real.pi ^ (-(5 / 2 : ℝ)) * (-1) at h
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨F, hF, _hmean, _hGamma, _hHasSum, _hOriginal, hTheta⟩ :=
    actual_h6_mean_zero_positive_fullTheta_excess_all_gamma_domains
  have hU := (actual_h6_fullTheta_excess_bound F hF).1
  have hsq := (memLp_two_iff_integrable_sq_norm hU.1.aestronglyMeasurable).1 hU.1
  have hexcess : IntegrableOn (fun x : ℝ =>
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2) (Ioi Real.pi) := by
    have hd := hU.2.sub hsq
    change Integrable (fun x : ℝ =>
      (x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 - ‖fullTheta F x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) at hd
    simpa only [IntegrableOn, sub_mul, one_mul] using hd
  have hcmp : (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2) ≤
      ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 := by
    apply integral_mono hexcess hU.2
    intro x
    nlinarith [sq_nonneg ‖fullTheta F x‖]
  have hraw : (∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2) =
      Real.pi ^ (6 : ℕ) * ∫ x : ℝ in Ioi Real.pi,
        (x / Real.pi) ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by field_simp [Real.pi_ne_zero]
  have hpos : 0 < ∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2 := by
    rw [hraw]
    exact mul_pos (pow_pos Real.pi_pos _) (hTheta.trans_le hcmp)
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), F, ?_⟩
  change (∫ x : ℝ in Ioi Real.pi,
    x ^ (6 : ℕ) * ‖fullTheta (fun _ : ℝ => (0 : ℂ)) x‖ ^ 2) ≠
      ∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2
  simpa only [fullTheta, physicalTerm, mul_zero, tsum_zero, norm_zero,
    zero_pow, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, integral_zero]
    using ne_of_lt hpos

def familyRegistration : Registration arena (type_of% (@actual_h6_gamma_profile_critical_exponential_l2_and_mass)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_h6_gamma_profile_critical_exponential_l2_and_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_h6_gamma_profile_critical_exponential_l2_and_mass) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2.GammaCriticalMass.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2.GammaCriticalMass.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => ∫ x : ℝ in Ioi Real.pi, x ^ (6 : ℕ) * ‖fullTheta F x‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end GammaCriticalMass

namespace ActualEvenBCriticalBudget

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ F =>
    ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (F : ℝ → ℂ) (_hF : originalPhysicalH6 F),
    Integrable (actualSuzukiEvenBProfile F) volume ∧
      MemLp (actualSuzukiEvenBProfile F) 2 volume ∧
      MemLp (fun r : ℝ => (Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) *
        actualSuzukiEvenBProfile F r) 2 volume ∧
      (∫ r : ℝ,
        ‖(Real.exp ((5 / 2 : ℝ) * |r|) : ℂ) * actualSuzukiEvenBProfile F r‖ ^ 2) ≤
        (68 / 25 : ℝ) * Real.pi ^ (7 / 2 : ℝ) *
          (∑' j : ℕ, ((((j + 1 : ℕ) : ℝ) ^ (3 : ℕ)))⁻¹) ^ 2 * R.readout () () F

private theorem source_reconstruction :
    (type_of% (@actual_h6_suzuki_even_b_l1_l2_critical_exponential)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := (hall (fun _ : ℝ => (0 : ℂ)) zero_h6).2.2.2
  have hs : 0 < ∑' j : ℕ, thetaModeCoefficient j := by
    exact lt_of_lt_of_le (by norm_num [thetaModeCoefficient] : 0 < thetaModeCoefficient 0)
      (thetaModeCoefficient_summable.le_tsum 0 (fun j _ => by
        unfold thetaModeCoefficient
        positivity))
  have hp : 0 < (68 / 25 : ℝ) * Real.pi ^ (7 / 2 : ℝ) *
      (∑' j : ℕ, thetaModeCoefficient j) ^ 2 := by positivity
  simp only [rejected, realize, zero_even_b, mul_zero, norm_zero, zero_pow,
    OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, integral_zero] at h
  change (0 : ℝ) ≤ (68 / 25 : ℝ) * Real.pi ^ (7 / 2 : ℝ) *
    (∑' j : ℕ, thetaModeCoefficient j) ^ 2 * (-1) at h
  nlinarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hcmp : (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖indicatorInput x‖ ^ 2) ≤
      ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖indicatorInput x‖ ^ 2 := by
    apply integral_mono indicator_excess_integrable indicator_h6.2
    intro x
    nlinarith [sq_nonneg ‖indicatorInput x‖]
  have hpos := indicator_excess_pos.trans_le hcmp
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change (∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖(0 : ℂ)‖ ^ 2) ≠
      ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖indicatorInput x‖ ^ 2
  simpa using ne_of_lt hpos

def familyRegistration : Registration arena (type_of% (@actual_h6_suzuki_even_b_l1_l2_critical_exponential)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_h6_suzuki_even_b_l1_l2_critical_exponential, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_h6_suzuki_even_b_l1_l2_critical_exponential) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2.ActualEvenBCriticalBudget.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2.ActualEvenBCriticalBudget.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => ∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ActualEvenBCriticalBudget

end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiExponentialL2
