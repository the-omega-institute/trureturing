import D5.S3.Arith.Primes.FiniteFibonacciRankClosure
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Finset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => fibonacciRankClosure S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p),
    let H := r.readout () () S
    rankClosureSeed S ⊆ H ∧
    (∀ p ∈ H, p.Prime) ∧
    (∀ p ∈ H, p ≤ max 5 (S.sup id)) ∧
    rankClosureStep H = H ∧
    (∀ K : Finset ℕ, rankClosureSeed S ⊆ K → rankClosureStep K ⊆ K → H ⊆ K)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h ∅ (by simp)).1
  have htwo : 2 ∈ rankClosureSeed (∅ : Finset ℕ) := by
    simp [rankClosureSeed]
  have hfalse : 2 ∈ (∅ : Finset ℕ) := by
    exact hbad htwo
  simp at hfalse

def registration : Registration arena
    (∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p),
      let H := fibonacciRankClosure S
      rankClosureSeed S ⊆ H ∧
      (∀ p ∈ H, p.Prime) ∧
      (∀ p ∈ H, p ≤ max 5 (S.sup id)) ∧
      rankClosureStep H = H ∧
      (∀ K : Finset ℕ, rankClosureSeed S ⊆ K → rankClosureStep K ⊆ K → H ⊆ K)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_fibonacci_rank_closure, rejected, rejected_law⟩
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
    have hS7 : ∀ p ∈ ({7} : Finset ℕ), p.Prime ∧ 5 < p := by
      intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      decide
    have h7 : 7 ∈ fibonacciRankClosure ({7} : Finset ℕ) :=
      (finite_fibonacci_rank_closure {7} hS7).1 (by simp [rankClosureSeed])
    have hEmpty : ∀ p ∈ fibonacciRankClosure (∅ : Finset ℕ), p ≤ 5 := by
      intro p hp
      have h := (finite_fibonacci_rank_closure ∅ (by simp)).2.2.1 p hp
      simpa using h
    refine ⟨(), (∅ : Finset ℕ), ({7} : Finset ℕ), ?_⟩
    change fibonacciRankClosure ∅ ≠ fibonacciRankClosure {7}
    intro heq
    rw [← heq] at h7
    have hbad := hEmpty 7 h7
    omega

register_information_theorem
  _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.finite_fibonacci_rank_closure
  in arena
  readout via (realize signature (fun _ _ S => fibonacciRankClosure S) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
