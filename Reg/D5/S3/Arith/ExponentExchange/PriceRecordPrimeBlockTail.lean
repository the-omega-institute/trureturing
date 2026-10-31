import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
import Reg.Support.DependentFamily

/-! Source-bound audit of the simultaneous prime-block tail inequality. -/

open _root_.D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (layerTail)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ lambda => lambda) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Only the price multiplying the conclusion's logarithmic exchange gap is
observed. The record remains at the original price, and the complete source
telescope, empty-block case and both conclusion clauses remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m P k : ℕ} {lambda : ℝ}
    (S : Finset ℕ) (_hm : 0 < m)
    (_hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m)
    (_hP : P.Prime) (_hPm : P ∣ m) (_hS : ∀ q ∈ S, q.Prime)
    (_hk : 1 ≤ k) (_hsmall : (∏ q ∈ S, q) ^ k < P),
    (∑ q ∈ S, (1 - (q : ℝ)⁻¹ ^ k) * layerTail m q) +
        R.readout () () lambda *
          (Real.log P - (k : ℝ) * Real.log (∏ q ∈ S, q : ℕ)) <
      goldenLayerMarginal P (m.factorization P) * Real.log P ∧
      goldenLayerMarginal P (m.factorization P) * Real.log P ≤ 1 / (P : ℝ)

private theorem first_two_layer :
    goldenLayerMarginal 2 1 * Real.log (2 : ℝ) = Real.log (3 / 2 : ℝ) := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold goldenLayerMarginal
  norm_num only [Nat.cast_ofNat]
  rw [div_mul_cancel₀ _ hlog]

private theorem two_record_at_zero :
    ∀ n : ℕ, 0 < n → n < 2 →
      goldenResourceObjective 0 n < goldenResourceObjective 0 2 := by
  have hstep : goldenResourceObjective 0 2 - goldenResourceObjective 0 1 =
      goldenLayerMarginal 2 1 * Real.log (2 : ℝ) := by
    simpa using golden_resource_objective_single_layer_delta (0 : ℝ)
      (n := 1) (p := 2) (by norm_num) (by norm_num)
  rw [first_two_layer] at hstep
  have hpos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  intro n hn hnm
  have hn1 : n = 1 := by omega
  subst n
  linarith

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (m := 2) (P := 2) (k := 1) (lambda := 0) ∅
    (by norm_num) two_record_at_zero (by norm_num) (by norm_num)
    (by simp) (by norm_num) (by norm_num)
  have hf : (2 : ℕ).factorization 2 = 1 :=
    (by norm_num : Nat.Prime 2).factorization_self
  have hbad : Real.log (2 : ℝ) <
      goldenLayerMarginal 2 1 * Real.log (2 : ℝ) := by
    simpa [rejected, realize, hf] using hh.1
  rw [first_two_layer] at hbad
  have hreverse : Real.log (3 / 2 : ℝ) < Real.log (2 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

def family : Registration arena (type_of% @price_record_prime_block_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@price_record_prime_block_tail, rejected, rejected_law⟩
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
    change (0 : ℝ) ≠ 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@price_record_prime_block_tail) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail.price_record_prime_block_tail.audit
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ lambda => lambda) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.ExponentExchange.PriceRecordPrimeBlockTail
