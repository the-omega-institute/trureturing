/- GID: D5/S3/Arith/Additive/RepresentationFunction
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/RepresentationFunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Ordered additive representation counts have total mass equal to the square of the set cardinality. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

namespace D5.S3.Arith.Additive.RepresentationFunction

/-- The number of ordered pairs of members of `A` whose sum is `n`. -/
def repCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A.product A).filter fun p => p.1 + p.2 = n).card

/-- The number of unordered pairs from `A` with sum `n`, allowing repeated members. -/
def repCountUnordered (A : Finset ℕ) (n : ℕ) : ℕ :=
  ((A.product A).filter fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n).card

/-- Summing over all reachable sums counts each ordered pair from `A` exactly once. -/
theorem repCount_total_mass (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) :
    ∑ n ∈ Finset.range (2 * N + 1), repCount A n = A.card ^ 2 := by
  have hsum : ∀ p ∈ A.product A, p.1 + p.2 ∈ Finset.range (2 * N + 1) := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have haN := Finset.mem_range.mp (hA ha)
    have hbN := Finset.mem_range.mp (hA hb)
    apply Finset.mem_range.mpr
    omega
  calc
    ∑ n ∈ Finset.range (2 * N + 1), repCount A n = (A.product A).card :=
      (Finset.card_eq_sum_card_fiberwise hsum).symm
    _ = A.card ^ 2 := (Finset.card_product A A).trans (Nat.pow_two A.card).symm

end D5.S3.Arith.Additive.RepresentationFunction
