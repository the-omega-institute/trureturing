import D5.S1.Recurrence.FibonacciDistinctSumWithOneClassification
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S1.Recurrence.FibonacciDistinctSumWithOneClassification

open _root_.D5.S1.Recurrence.FibonacciDistinctSumWithOneClassification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => ∑ x ∈ S, x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete classification is retained; only the sum tested for Fibonacci membership varies. -/
def arena : Arena where
  signature := signature
  Law a := ∀ S : Finset ℕ,
    (∀ x ∈ S, PositiveFibonacci x) → 1 ∈ S →
    (PositiveFibonacci (a.readout () () S) ↔ ∃ r, 1 ≤ r ∧ S = alternatingSet r) ∧
    (∀ r, 1 ≤ r → S = alternatingSet r →
      (∑ x ∈ S, x) = Nat.fib (2 * r) ∧
      ∀ t, 1 ≤ t → S = alternatingSet t → t = r)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hvalues : ∀ x ∈ ({1} : Finset ℕ), PositiveFibonacci x := by
    intro x hx
    have hx1 : x = 1 := Finset.mem_singleton.mp hx
    exact ⟨2, by omega, by simp [hx1]⟩
  have hzero := (h {1} hvalues (by simp)).1.mpr
    ⟨1, by omega, by norm_num [alternatingSet]⟩
  change PositiveFibonacci 0 at hzero
  rcases hzero with ⟨n, hn, heq⟩
  have := Nat.fib_pos.mpr (show 0 < n by omega)
  omega

def registration : Registration arena
    (∀ S : Finset ℕ, (∀ x ∈ S, PositiveFibonacci x) → 1 ∈ S →
      (PositiveFibonacci (∑ x ∈ S, x) ↔ ∃ r, 1 ≤ r ∧ S = alternatingSet r) ∧
      (∀ r, 1 ≤ r → S = alternatingSet r →
        (∑ x ∈ S, x) = Nat.fib (2 * r) ∧
        ∀ t, 1 ≤ t → S = alternatingSet t → t = r)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨classification, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i
      cases j
      exact False.elim (h rfl)
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (∅ : Finset ℕ), ({1} : Finset ℕ), ?_⟩
    change (∑ x ∈ (∅ : Finset ℕ), x) ≠ ∑ x ∈ ({1} : Finset ℕ), x
    simp

register_information_theorem classification in arena
  readout via (realize signature (fun _ _ S => ∑ x ∈ S, x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Recurrence.FibonacciDistinctSumWithOneClassification
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms classification
#print axioms registration

end Reg.D5.S1.Recurrence.FibonacciDistinctSumWithOneClassification
