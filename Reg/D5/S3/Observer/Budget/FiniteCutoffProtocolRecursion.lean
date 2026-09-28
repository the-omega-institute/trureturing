import D5.S3.Observer.Budget.FiniteCutoffProtocolRecursion
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Budget.FiniteCutoffProtocolRecursion

open _root_.D5.S3.Observer.Budget.FiniteCutoffProtocolRecursion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- Candidate multiplicity is the zero-query obstruction within the full cutoff law. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Finset Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => A.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p P : Nat) (_hp : 2 ≤ p) (b : Fin p) (A : Finset Nat)
    (_hne : A.Nonempty) (_hA : ∀ r ∈ A, r < P) (n D : Nat) (_hn : n ≤ D) (q : Nat),
    (FiniteCutoff p P b.val 0 A n D ↔ R.readout () () A = 1) ∧
    (FiniteCutoff p P b.val (q + 1) A n D ↔
      A.card = 1 ∨ ∃ t, n ≤ t ∧ t ≤ D ∧
        ∀ y ∈ A.image (response p P b.val t),
          FiniteCutoff p P b.val q (responseFiber p P b.val A t y) t D)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 2 1 (by decide) 0 {0} (by simp)
    (by intro r hr; simp only [Finset.mem_singleton] at hr; omega) 0 0 le_rfl 0).1
  have good : FiniteCutoff 2 1 0 0 {0} 0 0 := by
    refine ⟨.stop 0, ?_⟩
    intro r hr
    simp only [Finset.mem_singleton] at hr
    subst r
    exact ⟨rfl, le_rfl⟩
  exact Nat.zero_ne_one (bad.mp good)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_cutoff_branch_recursion, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), ∅, {0}, ?_⟩
    exact Nat.zero_ne_one

register_information_theorem finite_cutoff_branch_recursion in arena
  readout via (realize signature (fun _ _ A => A.card) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.Budget.FiniteCutoffProtocolRecursion
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Observer.Budget.FiniteCutoffProtocolRecursion
