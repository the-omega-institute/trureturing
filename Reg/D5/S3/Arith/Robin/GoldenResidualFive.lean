import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GoldenResidualFive
import D5.S3.Arith.GoldenResource.GoldenCell5040Congruence
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.GoldenResidualFive

open _root_.D5.S3.Arith.Robin.GoldenResidualFive
open _root_.D5.S3.Arith.GoldenResource.GoldenCell5040Congruence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The outer logarithm is the varied readout of Robin's capacity. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev coreArena : Arena where
  signature := signature
  Law R := ∀ (a b r : ℕ), 4 ≤ a → a ≤ 6 → 2 ≤ b → b ≤ 3 →
    r.Coprime 210 → ¬11 ∣ r → r.primeFactors.card ≤ 5 →
    5040 < 2 ^ a * 3 ^ b * 5 * 7 * r →
    (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 * 7 * r) : ℝ) /
        (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ) <
      Real.exp Real.eulerMascheroniConstant *
        R.readout () () (Real.log (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ))

abbrev congruenceArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → 5040 ∣ n → Nat.ModEq n (3 ^ n) 2241 →
    n.primeFactors.card ≤ 9 →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

abbrev thirtyNineArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → 5040 ∣ n → Nat.ModEq n (3 ^ n) 2241 →
    n.primeFactors.card ≤ 39 →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

abbrev sizeArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → 5040 ∣ n → Nat.ModEq n (3 ^ n) 2241 →
    Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ)) ≤
      (ArithmeticFunction.sigma 1 n : ℝ) / n → 5040 * 47 ^ 36 ≤ n

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_core_law : ¬ coreArena.Law rejected := by
  intro h
  have hbad := h 5 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide) (by simp) (by norm_num)
  change (ArithmeticFunction.sigma 1 (2 ^ 5 * 3 ^ 2 * 5 * 7 * 1) : ℝ) /
      (2 ^ 5 * 3 ^ 2 * 5 * 7 * 1 : ℕ) < Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

theorem rejected_congruence_law : ¬ congruenceArena.Law rejected := by
  intro h
  have hmod := goldenCell5040_modEq_2241 10080 (by decide)
  have hcard : (10080 : ℕ).primeFactors.card ≤ 9 := by
    rw [show (10080 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 * 7 by norm_num,
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_mul (by decide) (by decide),
      Nat.primeFactors_prime_pow (by decide) Nat.prime_two,
      Nat.primeFactors_prime_pow (by decide) Nat.prime_three,
      (by decide : Nat.Prime 5).primeFactors, (by decide : Nat.Prime 7).primeFactors]
    decide
  have hbad := h (n := 10080) (by norm_num) (by decide) hmod hcard
  change (ArithmeticFunction.sigma 1 10080 : ℝ) / (10080 : ℕ) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))

theorem rejected_thirty_nine_law : ¬ thirtyNineArena.Law rejected := by
  intro h
  apply rejected_congruence_law
  intro n hn h5040 hmod hcard
  exact h hn h5040 hmod (hcard.trans (by decide))

theorem rejected_size_law : ¬ sizeArena.Law rejected := by
  intro h
  have hmod := goldenCell5040_modEq_2241 10080 (by decide)
  have hbad : Real.exp Real.eulerMascheroniConstant *
      rejected.readout () () (Real.log (10080 : ℝ)) ≤
        (ArithmeticFunction.sigma 1 10080 : ℝ) / (10080 : ℕ) := by
    change Real.exp Real.eulerMascheroniConstant * 0 ≤ _
    rw [mul_zero]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbound := h (n := 10080) (by norm_num) (by decide) hmod hbad
  norm_num at hbound

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num)).ne

def coreRegistration : Registration coreArena (type_of% robin_of_core_residual_le_five) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_of_core_residual_le_five, rejected, rejected_core_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_core_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def congruenceRegistration : Registration congruenceArena
    (type_of% (@robin_of_modEq_2241_card_le_nine)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_of_modEq_2241_card_le_nine, rejected, rejected_congruence_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_congruence_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def thirtyNineRegistration : Registration thirtyNineArena
    (type_of% (@robin_of_modEq_2241_card_le_thirty_nine)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_of_modEq_2241_card_le_thirty_nine, rejected, rejected_thirty_nine_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_thirty_nine_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def sizeRegistration : Registration sizeArena
    (type_of% (@counterexample_size_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨counterexample_size_lower_bound, rejected, rejected_size_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_size_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def coreAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_of_core_residual_le_five)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.GoldenResidualFive.robin_of_core_residual_le_five.audit
  realizationName := `Reg.D5.S3.Arith.Robin.GoldenResidualFive.coreRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨coreArena⟩
  objectArena := .source ⟨coreArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coreArena ⟨coreRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GoldenResidualFive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body",
        "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def congruenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_of_modEq_2241_card_le_nine)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.GoldenResidualFive.robin_of_modEq_2241_card_le_nine.audit
  realizationName := `Reg.D5.S3.Arith.Robin.GoldenResidualFive.congruenceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨congruenceArena⟩
  objectArena := .source ⟨congruenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source congruenceArena ⟨congruenceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GoldenResidualFive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def thirtyNineAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_of_modEq_2241_card_le_thirty_nine)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.GoldenResidualFive.robin_of_modEq_2241_card_le_thirty_nine.audit
  realizationName := `Reg.D5.S3.Arith.Robin.GoldenResidualFive.thirtyNineRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨thirtyNineArena⟩
  objectArena := .source ⟨thirtyNineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source thirtyNineArena ⟨thirtyNineRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GoldenResidualFive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sizeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@counterexample_size_lower_bound)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.GoldenResidualFive.counterexample_size_lower_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.GoldenResidualFive.sizeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sizeArena⟩
  objectArena := .source ⟨sizeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sizeArena ⟨sizeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GoldenResidualFive
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Robin.GoldenResidualFive
