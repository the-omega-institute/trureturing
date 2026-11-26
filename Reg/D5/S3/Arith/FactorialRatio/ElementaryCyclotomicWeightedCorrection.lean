import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection
import Batteries.Tactic.OpenPrivate

/-! Source-bound observations of the weighted Chebyshev sum and factorial correction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection

open _root_.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection
open _root_.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd (levels)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset LeanInformationAudit
open scoped BigOperators

open private factorialCoefficient from D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection

abbrev signature : Signature where
  Params := ℕ → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem sensitive (law : Realization signature → Prop)
    (actual : Realization signature) (hAnchor : actual.anchor = rejected.anchor)
    (hBad : ¬ law rejected) : Sensitivity ⟨signature, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, hAnchor, hBad⟩
  · intro e
    exact nomatch e

abbrev psiArena : Arena where
  signature := signature
  Law R := ∀ (w : ℕ → ℝ) (x : ℕ),
    R.readout () w x = ∑ n ∈ Ioc 0 x, w n * ArithmeticFunction.vonMangoldt n

noncomputable def psiActual : Realization signature :=
  realize signature (fun _ w x => weightedPsi w x) (fun e => nomatch e)

private theorem psiRejected : ¬ psiArena.Law rejected := by
  intro h
  have bad := h (fun _ => 0) 0
  norm_num [rejected, realize] at bad

noncomputable def psiFamily : Registration psiArena (type_of% @weightedPsi_eq_sum_vonMangoldt) where
  actual := psiActual
  bridge := Iff.rfl
  variation := ⟨weightedPsi_eq_sum_vonMangoldt, rejected, psiRejected⟩
  sensitivity := sensitive psiArena.Law psiActual rfl psiRejected
  dependence := by
    intro role
    refine ⟨fun _ => 1, 0, 2, ?_⟩
    change weightedPsi (fun _ => 1) 0 ≠ weightedPsi (fun _ => 1) 2
    rw [weightedPsi_eq_sum_vonMangoldt, weightedPsi_eq_sum_vonMangoldt]
    have h : Ioc 0 2 = ({1, 2} : Finset ℕ) := by decide
    simpa [h, ArithmeticFunction.vonMangoldt_apply_prime (by decide : Nat.Prime 2)] using
      (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))).symm

noncomputable def psiAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedPsi_eq_sum_vonMangoldt) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection.weightedPsi_eq_sum_vonMangoldt.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection.psiFamily
  realizationSource := none
  generated := false
  arena := .source ⟨psiArena⟩
  objectArena := .source ⟨psiArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source psiArena ⟨psiFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w n => weightedPsi w n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "fn", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def correctionActual : Realization signature :=
  realize signature (fun _ w N => weightedK w N) (fun e => nomatch e)

private theorem correctionDependence : ObservationalDependence signature correctionActual := by
  intro role
  refine ⟨fun _ => 1, 0, 1, ?_⟩
  change weightedK (fun _ => 1) 0 ≠ weightedK (fun _ => 1) 1
  have hPrimes : Nat.primesLE 5 = ({2, 3, 5} : Finset ℕ) := by decide
  have hTwo : levels 2 5 = ({1, 2} : Finset ℕ) := by decide
  have hThree : levels 3 5 = ({1} : Finset ℕ) := by decide
  have hFive : levels 5 5 = ({1} : Finset ℕ) := by decide
  simpa [weightedK, primePowerReadout, hPrimes, hTwo, hThree, hFive, factorialCoefficient] using
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))).symm

abbrev carryArena : Arena where
  signature := signature
  Law R := ∀ (w : ℕ → ℝ) (N : ℕ),
    weightedB w N + R.readout () w N + weightedIndicator w N =
      ∑ i ∈ range (N + 1), weightedPsi w (4 * i + 1)

private theorem carryRejected : ¬ carryArena.Law rejected := by
  intro h
  have bad := h (fun _ => 0) 0
  norm_num [rejected, realize, weightedB, weightedIndicator, weightedPsi, primePowerReadout] at bad

noncomputable def carryFamily :
    Registration carryArena (type_of% @weightedB_add_weightedK_add_weightedIndicator) where
  actual := correctionActual
  bridge := Iff.rfl
  variation := ⟨weightedB_add_weightedK_add_weightedIndicator, rejected, carryRejected⟩
  sensitivity := sensitive carryArena.Law correctionActual rfl carryRejected
  dependence := correctionDependence

noncomputable def carryAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedB_add_weightedK_add_weightedIndicator) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection.weightedB_add_weightedK_add_weightedIndicator.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection.carryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨carryArena⟩
  objectArena := .source ⟨carryArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source carryArena ⟨carryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w n => weightedK w n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev errorArena : Arena where
  signature := signature
  Law R := ∀ (w : ℕ → ℝ) (W : ℝ),
    0 ≤ W → (∀ r, 0 ≤ w r) → (∀ r, w r ≤ W) → ∀ N : ℕ,
      |weightedB w N + R.readout () w N - ∑ i ∈ range (N + 1), weightedPsi w (4 * i)| ≤
        W * ((4 * (N : ℝ) + 1) * (Real.log 4 + 4))

private theorem errorRejected : ¬ errorArena.Law rejected := by
  intro h
  have bad := h (fun _ => 0) 0 le_rfl (fun _ => le_rfl) (fun _ => le_rfl) 0
  norm_num [rejected, realize, weightedB, weightedPsi, primePowerReadout] at bad

noncomputable def errorFamily : Registration errorArena (type_of% @corrected_weighted_sample_error) where
  actual := correctionActual
  bridge := Iff.rfl
  variation := ⟨corrected_weighted_sample_error, rejected, errorRejected⟩
  sensitivity := sensitive errorArena.Law correctionActual rfl errorRejected
  dependence := correctionDependence

noncomputable def errorAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@corrected_weighted_sample_error) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection.corrected_weighted_sample_error.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection.errorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨errorArena⟩
  objectArena := .source ⟨errorArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source errorArena ⟨errorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ w n => weightedK w n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
        stateBinder := 5
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.ElementaryCyclotomicWeightedCorrection
