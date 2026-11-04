import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.HigherValuationTail
import Reg.Support.DependentFamily

/-! Only the right-hand largest-prime argument varies. The full positive-price
record and the original repeated-prime sum remain at the original integer. -/

open _root_.D5.S3.Arith.Robin.PriceRecord.HigherValuationTail
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime layerTail)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.HigherValuationTail

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 2 ≤ m → ∀ {lambda : ℝ}, 0 < lambda →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
    (∑ p ∈ m.primeFactors.filter (fun p => 2 ≤ m.factorization p), layerTail m p) ≤
      6 / (largestPrime (R.readout () () m) : ℝ) ^ (2 / 3 : ℝ)

private theorem four_record_at_one_hundredth :
    ∀ n : ℕ, 0 < n → n < 4 →
      goldenResourceObjective (1 / 100) n < goldenResourceObjective (1 / 100) 4 := by
  have hgain : 1 / 7 ≤ Real.log (7 / 6 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 7 / 6)
    norm_num at hh ⊢
    exact hh
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hh ⊢
    exact hh
  have hlogdiff : Real.log (7 / 4 : ℝ) - Real.log (3 / 2 : ℝ) =
      Real.log (7 / 6 : ℝ) := by
    rw [← Real.log_div (by norm_num : (7 / 4 : ℝ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hscore : Real.log (3 / 2 : ℝ) <
      Real.log (7 / 4 : ℝ) - (1 / 100) * Real.log 4 := by linarith
  intro n hn hlt
  have hratio : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ 3 / 2 := by
    interval_cases n <;> norm_num [ArithmeticFunction.sigma] at *
  have hrpos : 0 < (ArithmeticFunction.sigma 1 n : ℝ) / n :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
      (by exact_mod_cast hn)
  have hlog := Real.log_le_log hrpos hratio
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hleft : 0 ≤ (1 / 100 : ℝ) * Real.log n := by positivity
  rw [golden_resource_sigma_identity _ (by omega : 1 ≤ n),
    golden_resource_sigma_identity _ (by norm_num : 1 ≤ (4 : ℕ))]
  have hs : (ArithmeticFunction.sigma 1 4 : ℝ) = 7 := by
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    norm_num [ArithmeticFunction.sigma, hdiv]
  rw [hs]
  linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (m := 4) (by norm_num) (lambda := 1 / 100) (by norm_num)
    four_record_at_one_hundredth
  have hfour : (4 : ℕ).primeFactors = {2} := by
    change ((2 : ℕ) ^ 2).primeFactors = {2}
    exact Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two
  have hval : (4 : ℕ).factorization 2 = 2 := by
    change ((2 : ℕ) ^ 2).factorization 2 = 2
    exact Nat.factorization_pow_self Nat.prime_two
  have hS : (4 : ℕ).primeFactors.filter (fun p => 2 ≤ (4 : ℕ).factorization p) = {2} := by
    simp only [hfour, Finset.filter_singleton, hval, le_refl, if_true]
  have htail : layerTail 4 2 = -Real.log (7 / 8 : ℝ) := by
    norm_num [layerTail, hval]
  have hpos : 0 < -Real.log (7 / 8 : ℝ) :=
    neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  have hzero : largestPrime 0 = 0 := by simp [largestPrime]
  have he : (0 : ℝ) ^ (2 / 3 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  simpa [rejected, realize, hS, htail, hzero, he, not_le.mpr hpos] using hbad

def family : Registration arena (type_of% @higher_valuation_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@higher_valuation_tail, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℕ) ≠ 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@higher_valuation_tail) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.HigherValuationTail.higher_valuation_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.HigherValuationTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.HigherValuationTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms higher_valuation_tail
#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.HigherValuationTail
