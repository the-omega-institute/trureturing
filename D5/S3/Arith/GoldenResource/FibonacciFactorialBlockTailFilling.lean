/- GID: D5/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial blocks realize exact rational tail filling while normalized capacities vanish at infinity. -/
import D5.S3.Arith.GoldenResource.RationalCapacityTailRealization
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

set_option autoImplicit false
open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.GoldenResource.FibonacciFactorialBlockTailFilling

open D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

/-- The Fibonacci row used by this chapter, indexed so that its first values are 1 and 2. -/
def G (n : ℕ) : ℕ := Nat.fib (n + 2)

/-- A separated family of finite factorial-divisible index blocks. -/
def BlockSpec (I : ℕ → Finset ℕ) : Prop :=
  I 0 = ∅ ∧ (∀ j, 0 < j → (I j).card = j * j.factorial) ∧
  (∀ j, 0 < j → ∀ n ∈ I j, j.factorial ∣ G n) ∧
  (∀ j k, 0 < j → j < k → ∀ n ∈ I j, ∀ m ∈ I k, n < m)

/-- Capacity obtained by dividing the Fibonacci row by the factorial of its block. -/
noncomputable def blockCapacity (I : ℕ → Finset ℕ) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, 0 < j ∧ n ∈ I j then G n / (Classical.choose h).factorial else 0

set_option maxHeartbeats 800000 in
/-- Separated factorial blocks fill all rational tails while their normalized capacities vanish. -/
theorem factorial_block_tail_filling :
    (∃ I : ℕ → Finset ℕ, BlockSpec I) ∧
    ∀ I : ℕ → Finset ℕ, BlockSpec I →
      FillsRationalTails G (blockCapacity I) ∧
      Filter.Tendsto (fun n => (blockCapacity I n : ℝ) / G n) Filter.atTop (nhds 0) ∧
      ¬ CofinalDivisibleCapacity G (blockCapacity I) := by
  classical
  have hG : ∀ n, 0 < G n := by
    intro n
    exact Nat.fib_pos.mpr (by omega)
  have hcof : ∀ d : ℕ, 0 < d → ∀ N : ℕ, ∃ n : ℕ, N < n ∧ d ∣ G n := by
    intro d hd N
    letI : NeZero d := ⟨hd.ne'⟩
    let T : ZMod d × ZMod d → ZMod d × ZMod d := fun x => (x.2, x.1 + x.2)
    let f : ℕ × ℕ → ℕ × ℕ := fun x => (x.2, x.1 + x.2)
    let C : ℕ × ℕ → ZMod d × ZMod d := fun x => (x.1, x.2)
    have hi : Function.Injective T := by
      intro a b h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp [T] at h₁ h₂
      apply Prod.ext
      · exact add_right_cancel (h₁ ▸ h₂)
      · exact h₁
    have hc : Function.Semiconj C f T := by
      intro x
      simp [C, f, T]
    have hcast (n : ℕ) : (Nat.fib n : ZMod d) = (T^[n] (0, 1)).1 := by
      have h := congrArg Prod.fst (hc.iterate_right n (0, 1))
      simpa [Nat.fib, f, C] using h
    obtain ⟨p, hp, hreturn⟩ := hi.mem_periodicPts (0, 1)
    have hz : (Nat.fib p : ZMod d) = 0 := by
      rw [hcast, hreturn.eq]
    have hdvd : d ∣ Nat.fib p := (ZMod.natCast_eq_zero_iff _ _).mp hz
    refine ⟨(N + 3) * p - 2, by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega : 2 ≤ (N + 3) * p)]
    exact hdvd.trans (Nat.fib_dvd p ((N + 3) * p) (dvd_mul_left p (N + 3)))
  sorry

end D5.S3.Arith.GoldenResource.FibonacciFactorialBlockTailFilling
