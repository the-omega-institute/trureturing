import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.PrefixNormalForm
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.ExponentExchange.PrefixNormalForm

open _root_.D5.S3.Arith.ExponentExchange.PrefixNormalForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: the size of a finite set of primes. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The arena varies the count of the companion's distinct primes; the count for `n` and every
other occurrence keep their actual values. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 1 ≤ n →
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ R.readout () () m.primeFactors = n.primeFactors.card ∧
      (∀ p q : ℕ, p.Prime → q.Prime → p < q → m.factorization q ≤ m.factorization p) ∧
      (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ (ArithmeticFunction.sigma 1 m : ℝ) / m

def actual : Realization signature :=
  realize signature (fun _ _ s => s.card) (fun e => nomatch e)

/-- The constant readout `0` replaces the companion's prime count. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- At `n = 2` the companion is at most 2 and the count for 2 is one, not zero. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, -, -, hm, -⟩ := h (n := 2) (by norm_num)
  change 0 = (Nat.primeFactors 2).card at hm
  rw [Nat.Prime.primeFactors Nat.prime_two, Finset.card_singleton] at hm
  exact absurd hm (by norm_num)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), ∅, {0}, ?_⟩
  change (∅ : Finset ℕ).card ≠ ({0} : Finset ℕ).card
  simp

def registration : Registration arena
    (∀ {n : ℕ}, 1 ≤ n →
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ m.primeFactors.card = n.primeFactors.card ∧
        (∀ p q : ℕ, p.Prime → q.Prime → p < q → m.factorization q ≤ m.factorization p) ∧
        (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ (ArithmeticFunction.sigma 1 m : ℝ) / m) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_antitone_exponent_form, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

/-- The record binds the companion's distinct-prime count through its raw source path, with
the dependent-family law and its four kernel obligations. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@exists_antitone_exponent_form)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => s.card)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.ExponentExchange.PrefixNormalForm.exists_antitone_exponent_form.audit
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.PrefixNormalForm.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ s => s.card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ExponentExchange.PrefixNormalForm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.ExponentExchange.PrefixNormalForm
