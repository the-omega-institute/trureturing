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
  classical
  let p (x : X A) (N : ℕ) : ℚ :=
    ∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℚ) / g n
  have hpcast (x : X A) (N : ℕ) : (p x N : ℝ) =
      ∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℝ) / g n := by
    simp only [p, Rat.cast_sum, Rat.cast_div, Rat.cast_natCast]
  have hread (u : B A) (s : Finset ℕ) (hs : u.property.toFinset ⊆ s) :
      weightedRead g u = ∑ n ∈ s, ((u.val n : ℕ) : ℚ) / g n := by
    apply Finset.sum_subset hs
    intro n _ hn
    have hz : (u.val n : ℕ) = 0 := by simpa using hn
    simp [hz]
  have hprefix (u : B A) (s : Finset ℕ) :
      (∑ n ∈ s, ((u.val n : ℕ) : ℚ) / g n) ≤ weightedRead g u := by
    rw [hread u (s ∪ u.property.toFinset) Finset.subset_union_right]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by
      intros; positivity)
  have hsub (x : X A) (c : ℝ) (hc : 0 ≤ c) :
      weightedTotal g x ≤ ENNReal.ofReal c ↔ ∀ N, (p x N : ℝ) ≤ c := by
    unfold weightedTotal
    simp only [← hpcast, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hc]
  have hupper (c : ℚ) (hc : 0 ≤ c) :
      closure (ambientLevel g A c) ⊆ {x | weightedTotal g x ≤ ENNReal.ofReal c} := by
    intro x hx
    apply (hsub x c (by exact_mod_cast hc)).mpr
    intro N
    have hcont : Continuous (fun y : X A => (p y N : ℝ)) := by
      simp only [hpcast]
      apply continuous_finsetSum
      intro n _
      exact ((continuous_of_discreteTopology : Continuous (fun z : Fin (A n + 1) =>
        ((z : ℕ) : ℝ))).comp (continuous_apply n)).div_const _
    apply closure_minimal (t := {y : X A | (p y N : ℝ) ≤ c}) ?_
      (isClosed_le hcont continuous_const) hx
    rintro y ⟨u, hu, rfl⟩
    exact (show (p u.val N : ℝ) ≤ (weightedRead g u : ℝ) by
      exact_mod_cast hprefix u (Finset.range (N + 1))).trans_eq hu
  sorry

#print axioms rational_tail_level_closure

end D5.S3.Arith.GoldenResource.RationalTailLevelClosure
