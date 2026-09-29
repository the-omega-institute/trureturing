import D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

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
  realize signature (fun _ _ n => padicValNat 5 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ H _ => padicValNat 5 (H.lcm fibonacciRank) + 2)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (H : Finset ℕ) (n : ℕ)
    (_hH : ∀ p ∈ H, p.Prime) (_hFive : 5 ∈ H) (_hn : 0 < n)
    (_hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
    (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H),
    r.readout () H n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hH : ∀ p ∈ ({5} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    decide
  have hIndex : ∀ p : ℕ, p.Prime → p ∣ 1 → p ∈ ({5} : Finset ℕ) := by
    intro p hp hpOne
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib 1 →
      Odd (padicValNat p (Nat.fib 1)) → p ∈ ({5} : Finset ℕ) := by
    intro p hp hpFib _
    have hpOne : p ∣ 1 := by simpa using hpFib
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hbad := h {5} 1 hH (by simp) (by decide) hIndex hOdd
  change padicValNat 5 (({5} : Finset ℕ).lcm fibonacciRank) + 2 ≤
    padicValNat 5 (({5} : Finset ℕ).lcm fibonacciRank) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (H : Finset ℕ) (n : ℕ)
      (_hH : ∀ p ∈ H, p.Prime) (_hFive : 5 ∈ H) (_hn : 0 < n)
      (_hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
      (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
        Odd (padicValNat p (Nat.fib n)) → p ∈ H),
      padicValNat 5 n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_five_adic_rank_budget, rejected, rejected_law⟩
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
    refine ⟨(∅ : Finset ℕ), (5 : ℕ), (25 : ℕ), ?_⟩
    change padicValNat 5 5 ≠ padicValNat 5 25
    have h5 : padicValNat 5 5 = 1 := by
      change padicValNat 5 (5 ^ 1) = 1
      exact padicValNat.prime_pow 1
    have h25 : padicValNat 5 25 = 2 := by
      change padicValNat 5 (5 ^ 2) = 2
      exact padicValNat.prime_pow 2
    omega

register_information_theorem
  _root_.D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget.fibonacci_five_adic_rank_budget
  in arena
  readout via (realize signature (fun _ _ n => padicValNat 5 n)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget
