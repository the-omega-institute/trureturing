import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.AbundancyRecord5040
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.ExponentExchange.AbundancyRecord5040

open _root_.D5.S3.Arith.ExponentExchange.AbundancyRecord5040
open _root_.D5.S3.Arith.GoldenResource.EightStepAbundancy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => (ArithmeticFunction.sigma 1 n : ℝ) / n) (fun e => nomatch e)

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

abbrev exchangeArena : Arena where
  signature := signature
  Law R := ∀ {m p q k : ℕ}, 0 < m → p.Prime → q.Prime → 1 ≤ k → q ∣ m →
    layerDenominator p k < q → m.factorization p < k →
    0 < (m / q) * p ∧ (m / q) * p < m ∧
      R.readout () () m < R.readout () () ((m / q) * p)

def exchangeRejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem exchange_rejected_law : ¬ exchangeArena.Law exchangeRejected := by
  intro h
  have hh := h (m := 3) (p := 2) (q := 3) (k := 1) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [layerDenominator]) (by norm_num [Nat.factorization])
  norm_num [exchangeRejected, realize] at hh

abbrev recordArena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 0 < m → 30 < R.readout () () m →
    (∀ n : ℕ, 0 < n → n < m → R.readout () () n < R.readout () () m) →
    5040 ∣ m

def recordRejected : Realization signature :=
  realize signature (fun _ _ n => if n = 31 then 31 else 0) (fun e => nomatch e)

theorem record_rejected_law : ¬ recordArena.Law recordRejected := by
  intro h
  have hh : 5040 ∣ 31 := h (m := 31) (by norm_num) (by norm_num [recordRejected, realize])
    (by
      intro n hn hnm
      have hne : n ≠ 31 := by omega
      norm_num [recordRejected, realize, hne])
  norm_num at hh

def exchangeFamily : Registration exchangeArena (type_of% @one_layer_abundancy_exchange) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨one_layer_abundancy_exchange, exchangeRejected, exchange_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨exchangeRejected, ?_, rfl, exchange_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def exchangeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@one_layer_abundancy_exchange) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ExponentExchange.AbundancyRecord5040.one_layer_abundancy_exchange.audit
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.AbundancyRecord5040.exchangeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exchangeArena⟩
  objectArena := .source ⟨exchangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exchangeArena ⟨exchangeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.AbundancyRecord5040
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms exchangeFamily
#print axioms exchangeAudit

def recordFamily : Registration recordArena (type_of% @strict_abundancy_record_divisible_5040) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_abundancy_record_divisible_5040, recordRejected, record_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨recordRejected, ?_, rfl, record_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def recordAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_abundancy_record_divisible_5040) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ExponentExchange.AbundancyRecord5040.strict_abundancy_record_divisible_5040.audit
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.AbundancyRecord5040.recordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨recordArena⟩
  objectArena := .source ⟨recordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source recordArena ⟨recordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.AbundancyRecord5040
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms recordFamily
#print axioms recordAudit

end
end Reg.D5.S3.Arith.ExponentExchange.AbundancyRecord5040
