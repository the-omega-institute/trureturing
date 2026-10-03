import D5.S3.Arith.Primes.FibonacciRankBudget
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciRankBudget

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciRankBudget
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
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (H : Finset ℕ) (n : ℕ)
    (_hH : ∀ p ∈ H, p.Prime)
    (_hTwo : 2 ∈ H) (_hThree : 3 ∈ H) (_hFive : 5 ∈ H)
    (_hClosed : rankClosureStep H = H) (_hn : 0 < n)
    (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H),
    r.readout () H n ∣ 5 * H.lcm fibonacciRank ∧
      (∀ q : ℕ, q.Prime → q ≠ 5 →
        padicValNat q n ≤ padicValNat q (H.lcm fibonacciRank)) ∧
      padicValNat 5 n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  let H := fibonacciRankClosure ∅
  have hs : ∀ p ∈ (∅ : Finset ℕ), p.Prime ∧ 5 < p := by simp
  have hc := finite_fibonacci_rank_closure ∅ hs
  have hTwo : 2 ∈ H := hc.1 (by simp [rankClosureSeed])
  have hThree : 3 ∈ H := hc.1 (by simp [rankClosureSeed])
  have hFive : 5 ∈ H := hc.1 (by simp [rankClosureSeed])
  have hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib 1 →
      Odd (padicValNat p (Nat.fib 1)) → p ∈ H := by
    intro p hp hpFib _
    have hpOne : p ∣ 1 := by simpa using hpFib
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hbad := (h H 1 hc.2.1 hTwo hThree hFive hc.2.2.2.1 (by decide) hOdd).1
  change 0 ∣ 5 * H.lcm fibonacciRank at hbad
  have hR : H.lcm fibonacciRank ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    intro p hp
    simp only [fibonacciRank, hc.2.1 p hp, dite_true]
    exact (rankWitness p (hc.2.1 p hp)).property.1.ne'
  exact (mul_ne_zero (by decide : (5 : ℕ) ≠ 0) hR) (Nat.zero_dvd.mp hbad)

def registration : Registration arena
    (∀ (H : Finset ℕ) (n : ℕ)
      (_hH : ∀ p ∈ H, p.Prime)
      (_hTwo : 2 ∈ H) (_hThree : 3 ∈ H) (_hFive : 5 ∈ H)
      (_hClosed : rankClosureStep H = H) (_hn : 0 < n)
      (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
        Odd (padicValNat p (Nat.fib n)) → p ∈ H),
      n ∣ 5 * H.lcm fibonacciRank ∧
        (∀ q : ℕ, q.Prime → q ≠ 5 →
          padicValNat q n ≤ padicValNat q (H.lcm fibonacciRank)) ∧
        padicValNat 5 n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_rank_budget, rejected, rejected_law⟩
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
    exact ⟨(∅ : Finset ℕ), (1 : ℕ), (2 : ℕ), by change (1 : ℕ) ≠ 2; decide⟩

register_information_theorem
  fibonacci_rank_budget
  in arena
  readout via (realize signature (fun _ _ n => n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.FibonacciRankBudget
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.FibonacciRankBudget
