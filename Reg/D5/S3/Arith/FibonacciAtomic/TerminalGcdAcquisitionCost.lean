import D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
import Reg.Support.DependentFamily

set_option autoImplicit false
open _root_.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ H => acquisitionCost H) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ H : ℕ, 1 ≤ H →
    IsLeast (acquisitionBudgets H) (if H = 1 then 0 else 2 * costBound H) ∧
    R.readout () () H = if H = 1 then 0 else 2 * costBound H

theorem binary_cost : acquisitionCost 2 = 2 := by
  have cost := (terminal_gcd_acquisition_cost 2 (by decide)).2
  have bound : costBound 2 = 1 := by
    simp only [costBound, Nat.prime_two.primeFactors, Finset.sup_singleton,
      Nat.prime_two.factorization_self]
  simpa only [show (2 : ℕ) ≠ 1 by decide, if_neg, ↓reduceIte, bound] using cost

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible := (h 2 (by decide)).2
  have bound : costBound 2 = 1 := by
    simp only [costBound, Nat.prime_two.primeFactors, Finset.sup_singleton,
      Nat.prime_two.factorization_self]
  norm_num [rejected, realize, bound] at impossible

noncomputable def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨terminal_gcd_acquisition_cost, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change acquisitionCost 1 ≠ acquisitionCost 2
    rw [(terminal_gcd_acquisition_cost 1 (by decide)).2, binary_cost]
    decide

register_information_theorem terminal_gcd_acquisition_cost in arena
  readout via (realize signature (fun _ _ H => acquisitionCost H) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
