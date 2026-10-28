import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer

open _root_.D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The smaller prime is a parameter; the quotient ranges over all natural states. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q u => u * q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the actual replacement integer varies. The complete source telescope,
prime hypotheses, record comparisons and all conclusion clauses remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m P q : ℕ} {lambda : ℝ}
    (hm : 0 < m) (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m)
    (hP : P.Prime) (hPm : P ∣ m) (hq : q.Prime) (hqP : q < P),
    let u := m / P
    let n := R.readout () q u
    let r := (q : ℝ)⁻¹ ^ (m.factorization q + 1)
    0 < n ∧ n < m ∧ u * P = m ∧
      u.factorization P + 1 = m.factorization P ∧
      u.factorization q = m.factorization q ∧
      goldenLayerMarginal q (m.factorization q + 1) * Real.log q +
          lambda * (Real.log P - Real.log q) <
        goldenLayerMarginal P (m.factorization P) * Real.log P ∧
      goldenLayerMarginal P (m.factorization P) * Real.log P ≤ 1 / (P : ℝ) ∧
      goldenLayerMarginal q (m.factorization q + 1) * Real.log q < 1 / (P : ℝ) ∧
      0 < r ∧ r ≤ 1 / (q : ℝ) ∧ (1 / (q : ℝ)) ≤ 1 / 2 ∧
      -Real.log (1 - r) < 2 / (P : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr : ∀ n : ℕ, 0 < n → n < 5040 →
      goldenResourceObjective (1 / 25) n < goldenResourceObjective (1 / 25) 5040 := by
    intro n hn hnm
    obtain ⟨hle, heq⟩ := golden_resource_unique_optimum hn
    rcases hle.eq_or_lt with he | hlt
    · exact ((Nat.ne_of_lt hnm) (heq.mp he)).elim
    · exact hlt
  have hbad := h (m := 5040) (P := 7) (q := 2) (lambda := 1 / 25)
    (by decide) (by norm_num) hr
    (by decide) (by norm_num) (by decide) (by decide)
  exact (by decide : ¬ 0 < (0 : ℕ)) hbad.1

def family : Registration arena (type_of% (@price_record_missing_layer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@price_record_missing_layer, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨2, 1, 2, ?_⟩
    change (1 : ℕ) * 2 ≠ 2 * 2
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@price_record_missing_layer) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer.price_record_missing_layer.audit
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q u => u * q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end

end Reg.D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
