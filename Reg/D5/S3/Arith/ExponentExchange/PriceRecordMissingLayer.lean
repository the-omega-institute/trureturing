import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer

open _root_.D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- The complete primality predicate, on arbitrary natural states. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n.Prime) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

/-- Both prime hypotheses vary together; all objective comparisons and conclusions
retain their original source meanings and quantifiers. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m P q : ℕ} {lambda : ℝ}
    (hm : 0 < m) (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m)
    (_hP : R.readout () () P) (hPm : P ∣ m) (_hq : R.readout () () q) (hqP : q < P),
    let u := m / P
    let n := u * q
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
  have hbad := h (m := 1) (P := 1) (q := 0) (lambda := 1)
    (by decide) (by norm_num) (by intro n hn hnm; omega)
    trivial (dvd_refl 1) trivial (by decide)
  exact (by norm_num : ¬ 0 < (1 / 1 : ℕ) * 0) hbad.1

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
    refine ⟨(), 2, 1, ?_⟩
    change Nat.Prime 2 ≠ Nat.Prime 1
    intro he
    exact Nat.not_prime_one (Eq.mp he Nat.prime_two)

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
  readout := some (realize signature (fun _ _ n => n.Prime) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end

end Reg.D5.S3.Arith.ExponentExchange.PriceRecordMissingLayer
