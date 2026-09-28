import D5.S3.Arith.Primes.FibonacciDyadicRankBudget
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciDyadicRankBudget

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciDyadicRankBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Finset ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => padicValNat 2 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ H _ => padicValNat 2 (H.lcm fibonacciRank) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (H : Finset ℕ) (n : ℕ)
    (_hH : ∀ p ∈ H, p.Prime) (_hThree : 3 ∈ H) (_hn : 0 < n)
    (_hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
    (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H),
    r.readout () H n ≤ padicValNat 2 (H.lcm fibonacciRank)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hH : ∀ p ∈ ({3} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    decide
  have hIndex : ∀ p : ℕ, p.Prime → p ∣ 1 → p ∈ ({3} : Finset ℕ) := by
    intro p hp hpOne
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib 1 →
      Odd (padicValNat p (Nat.fib 1)) → p ∈ ({3} : Finset ℕ) := by
    intro p hp hpFib _
    have hpOne : p ∣ 1 := by simpa using hpFib
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hbad := h {3} 1 hH (by simp) (by decide) hIndex hOdd
  change padicValNat 2 (({3} : Finset ℕ).lcm fibonacciRank) + 1 ≤
    padicValNat 2 (({3} : Finset ℕ).lcm fibonacciRank) at hbad
  omega

def registration : Registration arena
    (∀ (H : Finset ℕ) (n : ℕ)
      (_hH : ∀ p ∈ H, p.Prime) (_hThree : 3 ∈ H) (_hn : 0 < n)
      (_hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
      (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
        Odd (padicValNat p (Nat.fib n)) → p ∈ H),
      padicValNat 2 n ≤ padicValNat 2 (H.lcm fibonacciRank)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_dyadic_rank_budget, rejected, rejected_law⟩
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
    refine ⟨(∅ : Finset ℕ), (4 : ℕ), (8 : ℕ), ?_⟩
    change padicValNat 2 4 ≠ padicValNat 2 8
    have h4 : padicValNat 2 4 = 2 := by
      change padicValNat 2 (2 ^ 2) = 2
      exact padicValNat.prime_pow 2
    have h8 : padicValNat 2 8 = 3 := by
      change padicValNat 2 (2 ^ 3) = 3
      exact padicValNat.prime_pow 3
    omega

register_information_theorem
  _root_.D5.S3.Arith.Primes.FibonacciDyadicRankBudget.fibonacci_dyadic_rank_budget
  in arena
  readout via (realize signature (fun _ _ n => padicValNat 2 n)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciDyadicRankBudget
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciDyadicRankBudget
