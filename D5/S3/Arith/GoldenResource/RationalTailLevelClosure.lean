/- GID: D5/S3/Arith/GoldenResource/RationalTailLevelClosure
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/RationalTailLevelClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact rational tail filling gives sharp sublevel closures and nonclosed positive finite-state levels. -/
import D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.RationalTailLevelClosure

open Set Filter
open scoped Topology BigOperators
open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling (X B)
open D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

/-- The finite capacity states with a prescribed real value of their rational reading. -/
noncomputable def level (g A : ℕ → ℕ) (c : ℝ) : Set (B A) :=
  {u | (weightedRead g u : ℝ) = c}

/-- The image of a finite-state level in the full coordinate product. -/
noncomputable def ambientLevel (g A : ℕ → ℕ) (c : ℝ) : Set (X A) :=
  Subtype.val '' level g A c

set_option maxHeartbeats 800000 in
/-- Exact rational tail filling makes nonnegative rational level closures equal to sublevels
in both coordinate carriers, makes positive rational levels nonempty and nonclosed, and leaves
only the zero state at level zero and no finite states at negative or irrational levels. -/
theorem rational_tail_level_closure (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n) :
    (FillsRationalTails g A →
      (∀ c : ℚ, 0 ≤ c →
        closure (ambientLevel g A c) = {x | weightedTotal g x ≤ ENNReal.ofReal c} ∧
        closure (level g A c) = {u | (weightedRead g u : ℝ) ≤ c}) ∧
      (∀ c : ℚ, 0 < c → (level g A c).Nonempty ∧
        ¬ IsClosed (ambientLevel g A c) ∧ ¬ IsClosed (level g A c))) ∧
    (∀ c : ℝ, (c < 0 ∨ ¬ ∃ q : ℚ, (q : ℝ) = c) →
      level g A c = ∅ ∧ closure (level g A c) = ∅ ∧ closure (ambientLevel g A c) = ∅) ∧
    level g A 0 = {u | ∀ n, (u.val n : ℕ) = 0} ∧
    {x : X A | weightedTotal g x = 0} = {x | ∀ n, (x n : ℕ) = 0} := by
  sorry

#print axioms rational_tail_level_closure

end D5.S3.Arith.GoldenResource.RationalTailLevelClosure
