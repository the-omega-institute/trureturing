/- GID: D5/S3/Arith/GoldenResource/RationalCapacityTailRealization
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/RationalCapacityTailRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cofinal divisible capacities fill rational tails and exact tail filling realizes every extended nonnegative total. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

/-- rational reading for a positive integral denominator row. -/
noncomputable def weightedRead (g : ℕ → ℕ) {A : ℕ → ℕ} (u : B A) : ℚ :=
  ∑ n ∈ u.property.toFinset, ((u.val n : ℕ) : ℚ) / (g n : ℚ)

/-- the mass strictly after the cutoff, including possible infinity. -/
noncomputable def tailMass (g A : ℕ → ℕ) (N : ℕ) : ENNReal :=
  ∑' n, if N < n then ENNReal.ofReal ((A n : ℝ) / (g n : ℝ)) else 0

/-- one positive threshold works for every modulus and cutoff. -/
def CofinalDivisibleCapacity (g A : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℕ, 0 < d → ∀ N : ℕ,
    ∃ n : ℕ, N < n ∧ d ∣ g n ∧ ε ≤ (A n : ℝ) / (g n : ℝ)

/-- exact nonnegative rational filling by a legal finite tail. -/
def FillsRationalTails (g A : ℕ → ℕ) : Prop :=
  ∀ q : ℚ, 0 ≤ q → ∀ N : ℕ, ∃ u : B A,
    (∀ n : ℕ, n ≤ N → (u.val n : ℕ) = 0) ∧ weightedRead g u = q

/-- Cofinal divisible capacities fill every rational tail, and exact filling forces infinite tail mass. -/
theorem cofinal_capacity_rational_tail_filling (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n) :
    (CofinalDivisibleCapacity g A → FillsRationalTails g A) ∧
    (FillsRationalTails g A → ∀ N : ℕ, tailMass g A N = ⊤) := by
  sorry

/-- the exact extended supremum of the inclusive real partial sums. -/
noncomputable def weightedTotal (g : ℕ → ℕ) {A : ℕ → ℕ} (x : X A) : ENNReal :=
  ⨆ N : ℕ, ENNReal.ofReal
    (∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℝ) / (g n : ℝ))

/-- Every extended nonnegative real is the total reading of a capacity state when rational tails fill exactly. -/
theorem rational_tail_filling_full_range (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n)
    (hfill : FillsRationalTails g A) :
    Function.Surjective (@weightedTotal g A) := by
  sorry

end D5.S3.Arith.GoldenResource.RationalCapacityTailRealization
