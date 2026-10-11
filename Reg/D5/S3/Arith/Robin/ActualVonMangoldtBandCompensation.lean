import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators Interval ArithmeticFunction

namespace Reg.D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation

open _root_.D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
open _root_.D5.S3.Arith.Robin.QuotientIntegralBudget (arithmeticPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private theorem unit_centered (A t : ℝ) : centeredKernel A 1 t = 0 := by
  simp [centeredKernel, dilatedKernel]

private theorem unit_residual (A t : ℝ) : residualKernel A 1 t = 0 := by
  simp [residualKernel, regularKernel, plateau, smoothRemainder, unit_centered]

private theorem unit_volume (A : ℝ) : bandVolume A 1 = 0 := by
  simp [bandVolume, unit_residual]

private theorem unit_compensation (A : ℝ) : actualCompensation A 1 = 0 := by
  simp [actualCompensation, weightedPrefix, arithmeticPrefix, unit_residual]

private theorem unit_boundary (A R : ℝ) : smoothBoundary A 1 R = 0 := by
  have hs : smoothRemainder 1 = fun _ => (0 : ℝ) := by funext t; simp [smoothRemainder]
  simp [smoothBoundary, plateau, hs]

private theorem wide_theta (A : ℝ) (hA : 0 < A) :
    ThetaIncrementLower ((99 / 100 : ℝ) * A) (2 * ((99 / 100 : ℝ) * A)) 0 := by
  intro u v hu huv hv hd
  have hX : 0 < (99 / 100 : ℝ) * A := by positivity
  exfalso
  linarith

private theorem large_A : 0 < Real.exp (78 : ℝ) := Real.exp_pos _

private theorem response_zero_R (A c : ℝ) : finiteResponse A c 0 = 0 := by
  simp [finiteResponse, weightedPrefix, arithmeticPrefix]

private theorem response_small_R : finiteResponse 2 2 1 = -(1 / (4 * Real.log 2)) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hb : ∀ t ∈ uIcc (0 : ℝ) 1, centeredKernel 2 2 t = 1 / (4 * Real.log 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht2 : t ≤ (2 : ℝ) := by linarith [ht.2]
    have htc : t / 2 ≤ (2 : ℝ) := by linarith [ht.2]
    simp only [centeredKernel, dilatedKernel, maxKernel, tangentKernel, if_pos ht2,
      max_eq_left ht2, max_eq_left htc]
    norm_num
    field_simp [hl]
    <;> ring
  have hint : (∫ t in (0 : ℝ)..1, centeredKernel 2 2 t) = 1 / (4 * Real.log 2) := by
    rw [intervalIntegral.integral_congr hb]
    simp
  simp [finiteResponse, weightedPrefix, arithmeticPrefix, hint]

/-- Parameters retain A and c; the varying state is the original real R. -/
abbrev responseSignature : Signature where
  Params := Sigma (fun _ : ℝ => ℝ)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def responseActual : Realization responseSignature :=
  realize responseSignature (fun _ p R => finiteResponse p.1 p.2 R) (fun e => nomatch e)

def responseRejected : Realization responseSignature :=
  realize responseSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev identityArena : Arena where
  signature := responseSignature
  Law r := ∀ {A c R : ℝ}, Real.exp 78 ≤ A → (99 / 100 : ℝ) ≤ c →
    c ≤ (101 / 100 : ℝ) → A < R → c * A ≤ R →
      r.readout () ⟨A, c⟩ R = smoothBoundary A c R + bandVolume A c - actualCompensation A c

private theorem identity_rejected : ¬ identityArena.Law responseRejected := by
  intro h
  have ht := h (A := Real.exp 78) (c := 1) (R := Real.exp 78 + 1)
    le_rfl (by norm_num) (by norm_num) (by linarith) (by linarith)
  change (1 : ℝ) = _ at ht
  simp only [unit_boundary, unit_volume, unit_compensation] at ht
  norm_num at ht

private theorem response_dependence : ObservationalDependence responseSignature responseActual := by
  intro i
  refine ⟨⟨2, 2⟩, 0, 1, ?_⟩
  change finiteResponse 2 2 0 ≠ finiteResponse 2 2 1
  rw [response_zero_R, response_small_R]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < 1 / (4 * Real.log 2) := by positivity
  linarith

def identityFamily : Registration identityArena (type_of% (@finite_signed_response_identity)) where
  actual := responseActual
  bridge := Iff.rfl
  variation := ⟨@finite_signed_response_identity, responseRejected, identity_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨responseRejected, ?_, rfl, identity_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := response_dependence

def identityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_signed_response_identity) (type_of% (realize responseSignature responseActual.readout responseActual.anchor))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation.finite_signed_response_identity.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation.identityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨identityArena⟩
  objectArena := .source ⟨identityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source identityArena ⟨identityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize responseSignature responseActual.readout responseActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms identityRegistration

private theorem compensation_two_positive : 0 < actualCompensation 2 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hl34 : Real.log 3 < 2 * Real.log 2 := by
    rw [← hl4]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hz : 0 < Real.log 3 - Real.log 2 := by linarith
  have hΛ3 : Λ 3 = Real.log 3 := ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
  have he : actualCompensation 2 2 = Real.log 3 *
      (1 / (3 * (Real.log 3 - Real.log 2)) - 1 / (4 * Real.log 2)) := by
    norm_num [actualCompensation, weightedPrefix, arithmeticPrefix, bandHigh,
      Finset.sum_range_succ, residualKernel, regularKernel, centeredKernel, dilatedKernel,
      maxKernel, tangentKernel, plateau, smoothRemainder]
    rw [hl4, hΛ3]
    field_simp [hl2.ne', hl3.ne', hz.ne']
    <;> ring
  rw [he]
  apply mul_pos hl3
  apply sub_pos.mpr
  apply one_div_lt_one_div_of_lt (by positivity : 0 < 3 * (Real.log 3 - Real.log 2))
  linarith

abbrev compensationSignature : Signature where
  Params := Sigma (fun _ : ℝ => Sigma (fun _ : ℝ => ℝ))
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def compensationActual : Realization compensationSignature :=
  realize compensationSignature (fun _ p c => actualCompensation p.1 c) (fun e => nomatch e)

def compensationRejected : Realization compensationSignature :=
  realize compensationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev compensationArena : Arena where
  signature := compensationSignature
  Law r := ∀ {A c H ε : ℝ}, Real.exp 78 ≤ A → (99 / 100 : ℝ) ≤ c →
    c ≤ (101 / 100 : ℝ) → 0 < H → 0 ≤ ε → ε < 1 →
    ThetaIncrementLower ((99 / 100 : ℝ) * A) H ε →
      (1 - ε) * max 0 (bandVolume A c - shortAllowance A c H) ≤ r.readout () ⟨A, ⟨H, ε⟩⟩ c

private theorem compensation_rejected : ¬ compensationArena.Law compensationRejected := by
  intro h
  have ht := h (A := Real.exp 78) (c := 1) (H := 2 * ((99 / 100 : ℝ) * Real.exp 78)) (ε := 0)
    le_rfl (by norm_num) (by norm_num) (by positivity) le_rfl (by norm_num) (wide_theta _ large_A)
  change _ ≤ (-1 : ℝ) at ht
  simp [unit_volume, shortAllowance, min_eq_right (sq_nonneg _)] at ht
  norm_num at ht

def compensationFamily : Registration compensationArena
    (type_of% (@actual_vonMangoldt_band_compensation_of_theta_increment_lower)) where
  actual := compensationActual
  bridge := Iff.rfl
  variation := ⟨@actual_vonMangoldt_band_compensation_of_theta_increment_lower,
    compensationRejected, compensation_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨compensationRejected, ?_, rfl, compensation_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2, ⟨1, 0⟩⟩, 1, 2, ?_⟩
    change actualCompensation 2 1 ≠ actualCompensation 2 2
    rw [unit_compensation]
    exact (ne_of_gt compensation_two_positive).symm

def compensationRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_vonMangoldt_band_compensation_of_theta_increment_lower)
    (type_of% (realize compensationSignature compensationActual.readout compensationActual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation.actual_vonMangoldt_band_compensation_of_theta_increment_lower.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation.compensationFamily
  realizationSource := none
  generated := false
  arena := .source ⟨compensationArena⟩
  objectArena := .source ⟨compensationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source compensationArena ⟨compensationFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize compensationSignature compensationActual.readout compensationActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev consumerSignature : Signature where
  Params := Sigma (fun _ : ℝ => Sigma (fun _ : ℝ => Sigma (fun _ : ℝ => ℝ)))
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def consumerActual : Realization consumerSignature :=
  realize consumerSignature (fun _ p R => finiteResponse p.1 p.2.1 R) (fun e => nomatch e)

def consumerRejected : Realization consumerSignature :=
  realize consumerSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev consumerArena : Arena where
  signature := consumerSignature
  Law r := ∀ {A c R H ε : ℝ}, Real.exp 78 ≤ A → (99 / 100 : ℝ) ≤ c →
    c ≤ (101 / 100 : ℝ) → A < R → c * A ≤ R → 0 < H → 0 ≤ ε → ε < 1 →
    ThetaIncrementLower ((99 / 100 : ℝ) * A) H ε →
      r.readout () ⟨A, ⟨c, ⟨H, ε⟩⟩⟩ R ≤ smoothBoundary A c R + ε * bandVolume A c +
        (1 - ε) * shortAllowance A c H

private theorem consumer_rejected : ¬ consumerArena.Law consumerRejected := by
  intro h
  have ht := h (A := Real.exp 78) (c := 1) (R := Real.exp 78 + 1)
    (H := 2 * ((99 / 100 : ℝ) * Real.exp 78)) (ε := 0)
    le_rfl (by norm_num) (by norm_num) (by linarith) (by linarith) (by positivity)
    le_rfl (by norm_num) (wide_theta _ large_A)
  change (1 : ℝ) ≤ _ at ht
  simp [unit_boundary, unit_volume, shortAllowance, min_eq_right (sq_nonneg _)] at ht
  norm_num at ht

def consumerFamily : Registration consumerArena
    (type_of% (@finite_signed_response_upper_of_theta_increment_lower)) where
  actual := consumerActual
  bridge := Iff.rfl
  variation := ⟨@finite_signed_response_upper_of_theta_increment_lower, consumerRejected, consumer_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨consumerRejected, ?_, rfl, consumer_rejected⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2, ⟨2, ⟨1, 0⟩⟩⟩, 0, 1, ?_⟩
    change finiteResponse 2 2 0 ≠ finiteResponse 2 2 1
    rw [response_zero_R, response_small_R]
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hq : 0 < 1 / (4 * Real.log 2) := by positivity
    linarith

def consumerRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_signed_response_upper_of_theta_increment_lower)
    (type_of% (realize consumerSignature consumerActual.readout consumerActual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation.finite_signed_response_upper_of_theta_increment_lower.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation.consumerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨consumerArena⟩
  objectArena := .source ⟨consumerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source consumerArena ⟨consumerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize consumerSignature consumerActual.readout consumerActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
    definition := none
    coordinates := #[0, 1, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms compensationRegistration
#print axioms consumerRegistration

end Reg.D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
