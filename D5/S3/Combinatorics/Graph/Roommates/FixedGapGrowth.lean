/- GID: D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/FixedGapGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Subadditive]
   utility: none
   digest: Fixed-gap concatenation and splitting give one uniform exponential growth base. -/

import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace D5.S3.Combinatorics.Graph.Roommates.FixedGapGrowth

/-- The two Fekete applications turn a bounded additive defect into all-length bounds.
This lemma is an internal component of the full certificate-count route. -/
theorem additive_defect_bounds (f : ℕ → ℝ) (D : ℝ)
    (hzero : f 0 = 0) (hnonneg : ∀ n, 0 ≤ f n) (hD : 0 ≤ D)
    (hsub : Subadditive f) (hrev : ∀ n m, f n + f m ≤ f (n + m) + D) :
    ∃ h : ℝ, 0 ≤ h ∧ Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 h) ∧
      ∀ n, h * n ≤ f n ∧ f n ≤ h * n + D := by
  have hb : BddBelow (range (fun n => f n / (n : ℝ))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)⟩
  let h := hsub.lim
  have ht : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 h) := hsub.tendsto_lim hb
  have hpos : 0 ≤ h := ge_of_tendsto ht (Eventually.of_forall fun n =>
    div_nonneg (hnonneg n) (Nat.cast_nonneg n))
  let u : ℕ → ℝ := fun n => -f n + D
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [hrev n m]
  have hlin (n : ℕ) : f n ≤ (n : ℝ) * f 1 := by
    have hh := hsub.apply_mul_add_le n 1 0
    simpa [hzero] using hh
  have hub : BddBelow (range (fun n => u n / (n : ℝ))) := by
    refine ⟨-f 1, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr (hnonneg 1)
    · apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      dsimp [u]
      linarith [hlin n]
  have huT : Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 (-h)) := by
    have hd : Tendsto (fun n : ℕ => D / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hh := ht.neg.add hd
    simpa only [u, add_div, neg_div, add_zero] using hh
  have hulim : hu.lim = -h := tendsto_nhds_unique (hu.tendsto_lim hub) huT
  refine ⟨h, hpos, ht, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, hzero, hD]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  constructor
  · exact (le_div_iff₀ hnR).mp (hsub.lim_le_div hb hn)
  · have hh := hu.lim_le_div hub hn
    rw [hulim] at hh
    have hh' := (le_div_iff₀ hnR).mp hh
    dsimp [u] at hh'
    nlinarith

/-- A fixed gap can be absorbed as a bounded logarithmic defect, with no parity premise. -/
theorem fixed_gap_log_bounds (f : ℕ → ℝ) (g : ℕ)
    (hzero : f 0 = 0) (hnonneg : ∀ n, 0 ≤ f n)
    (hsub : Subadditive f)
    (hpad : ∀ n m, 0 < n → 0 < m → f n + f m ≤ f (n + m + g)) :
    ∃ h : ℝ, 0 ≤ h ∧ Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 h) ∧
      ∀ n, h * n ≤ f n ∧ f n ≤ h * n + f g := by
  apply additive_defect_bounds f (f g) hzero hnonneg (hnonneg g) hsub
  intro n m
  by_cases hn : n = 0
  · simp [hn, hzero, hnonneg g]
  by_cases hm : m = 0
  · simp [hm, hzero, hnonneg g]
  exact (hpad n m (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hm)).trans (hsub _ _)

#print axioms additive_defect_bounds
#print axioms fixed_gap_log_bounds

end D5.S3.Combinatorics.Graph.Roommates.FixedGapGrowth
