import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.FewDistinctPrimes
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.FewDistinctPrimes

open _root_.D5.S3.Arith.Robin.FewDistinctPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: the outer logarithm of the Robin capacity `exp γ · log (log n)`. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The capacity's outer logarithm varies; the divisor ratio and the inner logarithm stay. -/
abbrev eightArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → n.primeFactors.card ≤ 8 →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

abbrev rangeArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 5040 < n → n < 223092870 →
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * R.readout () () (Real.log (n : ℝ))

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

/-- The constant readout `0` replaces the outer logarithm. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem ratio_nonneg (n : ℕ) : 0 ≤ (ArithmeticFunction.sigma 1 n : ℝ) / n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem card_8192 : (Nat.primeFactors 8192).card ≤ 8 := by
  rw [show (8192 : ℕ) = 2 ^ 13 by norm_num, Nat.primeFactors_prime_pow (by norm_num)
    Nat.prime_two, Finset.card_singleton]
  norm_num

/-- At `n = 2^13` the zero readout would make a nonnegative ratio negative. -/
theorem rejected_eight_law : ¬ eightArena.Law rejected := by
  intro h
  have hbad := h (n := 8192) (by norm_num) card_8192
  change (ArithmeticFunction.sigma 1 8192 : ℝ) / (8192 : ℕ) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (ratio_nonneg 8192))

theorem rejected_range_law : ¬ rangeArena.Law rejected := by
  intro h
  have hbad := h (n := 8192) (by norm_num) (by norm_num)
  change (ArithmeticFunction.sigma 1 8192 : ℝ) / (8192 : ℕ) <
    Real.exp Real.eulerMascheroniConstant * 0 at hbad
  rw [mul_zero] at hbad
  exact absurd hbad (not_lt.mpr (ratio_nonneg 8192))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (by norm_num)).ne

def eightRegistration : Registration eightArena
    (∀ {n : ℕ}, 5040 < n → n.primeFactors.card ≤ 8 →
      (ArithmeticFunction.sigma 1 n : ℝ) / n <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_of_card_primeFactors_le_eight, rejected, rejected_eight_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_eight_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def rangeRegistration : Registration rangeArena
    (∀ {n : ℕ}, 5040 < n → n < 223092870 →
      (ArithmeticFunction.sigma 1 n : ℝ) / n <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robin_lt_223092870, rejected, rejected_range_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_range_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- Each record binds the outer logarithm of the capacity through its raw source path, with the
dependent-family law and its four kernel obligations. -/
def eightAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robin_of_card_primeFactors_le_eight)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FewDistinctPrimes.robin_of_card_primeFactors_le_eight.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FewDistinctPrimes.eightRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨eightArena⟩
  objectArena := .source ⟨eightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source eightArena ⟨eightRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FewDistinctPrimes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def rangeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@robin_lt_223092870)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.FewDistinctPrimes.robin_lt_223092870.audit
  realizationName := `Reg.D5.S3.Arith.Robin.FewDistinctPrimes.rangeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rangeArena⟩
  objectArena := .source ⟨rangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rangeArena ⟨rangeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ x => Real.log x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.FewDistinctPrimes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Robin.FewDistinctPrimes
