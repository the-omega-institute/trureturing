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
  sorry

end D5.S3.Arith.GoldenResource.FibonacciFactorialBlockTailFilling
