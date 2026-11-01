import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
import Reg.Support.DependentFamily

/-! Source-bound audit of the uniform prime-power envelope. -/

open _root_.D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope

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

/-- Only the argument of the largest prime on the right is observed.
The original record, price, divisor and valuation remain at the original m. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 2 ≤ m → ∀ {lambda : ℝ}, 0 ≤ lambda →
    (∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
    ∀ p : ℕ, p.Prime → p ∣ m →
      p ^ m.factorization p < 4 * (largestPrime (R.readout () () m)) ^ 2

private theorem two_record_at_zero :
    ∀ n : ℕ, 0 < n → n < 2 →
      goldenResourceObjective 0 n < goldenResourceObjective 0 2 := by
  intro n hn hnm
  have hn1 : n = 1 := by omega
  subst n
  rw [golden_resource_sigma_identity 0 (by norm_num),
    golden_resource_sigma_identity 0 (by norm_num)]
  have hs2 : ArithmeticFunction.sigma 1 2 = 3 := by
    have h := ArithmeticFunction.sigma_one_apply_prime_pow
      (i := 1) (by norm_num : Nat.Prime 2)
    norm_num [Finset.sum_range_succ] at h ⊢
    exact h
  simp only [zero_mul, sub_zero, ArithmeticFunction.sigma_one, Nat.cast_one, div_one,
    Real.log_one, hs2]
  exact Real.log_pos (by norm_num)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (m := 2) (by norm_num) (lambda := 0) (by norm_num)
    two_record_at_zero 2 (by norm_num) (by norm_num)
  have hf : (2 : ℕ).factorization 2 = 1 :=
    (by norm_num : Nat.Prime 2).factorization_self
  change 2 ^ (2 : ℕ).factorization 2 < 4 * largestPrime 0 ^ 2 at hbad
  norm_num [hf, largestPrime] at hbad

def family : Registration arena (type_of% @price_record_prime_power_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@price_record_prime_power_envelope, rejected, rejected_law⟩
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
    (@price_record_prime_power_envelope) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope.price_record_prime_power_envelope.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
