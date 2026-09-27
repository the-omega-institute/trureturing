import D5.S3.Arith.Primes.OriginalOddDepthSupport
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.OriginalOddDepthSupport
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
  Law r := ∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p)
    (n : ℕ) (_hn : 0 < n) (_hBlock : PrimeIndexOddFactor n)
    (_hVal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
      padicValNat p (Nat.fib n) = padicValNat p (Nat.fib (fibonacciRank p)))
    (_hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
      Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S),
    let H := r.readout () () S
    (∀ ell : ℕ, ell.Prime → ell ∣ n → ell ∈ H) ∧
    oddDepthKernel n ∣ H.prod id

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hBlock2 : PrimeIndexOddFactor 2 := by
    intro ell _ hlarge hdiv
    have hle : ell ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hExternal2 : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib 2 →
      ¬ p ∣ 2 → Odd (padicValNat p (Nat.fib (fibonacciRank p))) →
      p ∈ (∅ : Finset ℕ) := by
    intro p hp _ hdiv _ _
    have hpOne : p ∣ 1 := by simpa using hdiv
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hVal2 : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib 2 → ¬ p ∣ 2 →
      padicValNat p (Nat.fib 2) = padicValNat p (Nat.fib (fibonacciRank p)) := by
    intro p hp _ hdiv _
    have hpOne : p ∣ 1 := by simpa using hdiv
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hbad := (h ∅ (by simp) 2 (by decide) hBlock2 hVal2 hExternal2).1
    2 Nat.prime_two (dvd_refl 2)
  change 2 ∈ (∅ : Finset ℕ) at hbad
  simp at hbad

def registration : Registration arena
    (∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p)
      (n : ℕ) (_hn : 0 < n) (_hBlock : PrimeIndexOddFactor n)
      (_hVal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
        padicValNat p (Nat.fib n) = padicValNat p (Nat.fib (fibonacciRank p)))
      (_hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S),
      let H := fibonacciRankClosure S
      (∀ ell : ℕ, ell.Prime → ell ∣ n → ell ∈ H) ∧
      oddDepthKernel n ∣ H.prod id) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_odd_depth_support, rejected, rejected_law⟩
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
  _root_.D5.S3.Arith.Primes.OriginalOddDepthSupport.original_odd_depth_support
  in arena
  readout via (realize signature (fun _ _ S => fibonacciRankClosure S) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.OriginalOddDepthSupport
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport
