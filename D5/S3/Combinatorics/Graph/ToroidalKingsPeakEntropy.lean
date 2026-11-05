/- GID: D5/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ToroidalKingsPeakEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Toroidal king modal coefficients have the literal square-tiling growth constant. -/
import D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam

/-! # Toroidal king peak entropy

The constant is the limit of the A063443 square-tiling sequence, with its literal
square-area normalization. It is defined independently of the toroidal sequence.
The maximum ranges over every cardinality and the final statement includes all
integers at least three, with no parity restriction.
-/

namespace D5.S3.Combinatorics.Graph.ToroidalKingsPeakEntropy

open ToroidalKingsEmptySeam Filter
open scoped Topology

noncomputable section

/-- Positive real square-area root, with natural counts cast before exponentiation. -/
def rootGrowth (a : ℕ → ℕ) (n : ℕ) : ℝ := (a n : ℝ) ^ ((n : ℝ) ^ 2)⁻¹

/-- OEIS A247413, bound to the A063443 tiling limit rather than to toroidal counts. -/
def a247413 : ℝ := limUnder atTop (rootGrowth a063443)

private theorem count_pos (n : ℕ) : 0 < torusCount n := by
  apply Finset.card_pos.mpr
  exact ⟨∅, by simp [independentSets]⟩

private theorem free_pos (n : ℕ) : 0 < freeCount n := by
  apply Finset.card_pos.mpr
  exact ⟨∅, by simp [independentSets]⟩

private theorem peak_pos (n : ℕ) : 0 < peak n := by
  have h := count_le_mul_peak n
  have hp := count_pos n
  by_contra hn
  have hz : peak n = 0 := by omega
  simp only [hz, mul_zero] at h
  omega

private theorem shifted_log_limit (a : ℕ → ℕ) {s : ℝ}
    (h : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => Real.log (a (n - 1) : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 s) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hi
  have hh := (h.comp (tendsto_sub_atTop_nat 1)).mul (hr.pow 2)
  simp only [one_pow, mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : (n : ℝ) - 1 ≠ 0 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (show 1 ≤ n by omega) (R := ℝ)
  dsimp
  rw [hc]
  field_simp [hn0, hm0]

private theorem polynomial_log_loss :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) ^ 2 + 1) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hx
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (1 : ℝ) + (1 / n) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hi.pow 2)
  have hmul := hlog.mul hratio
  simp only [zero_mul] at hmul
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx0 : (n : ℝ) ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  dsimp
  field_simp [hn0, hx0]

private theorem peak_log_limit {s : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (freeCount n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => Real.log (peak n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 s) := by
  have hl := (shifted_log_limit freeCount hf).sub polynomial_log_loss
  simp only [sub_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hf
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (0 : ℝ) < peak n := by exact_mod_cast peak_pos n
    have hfpos : (0 : ℝ) < freeCount (n - 1) := by exact_mod_cast free_pos (n - 1)
    have hle : freeCount (n - 1) ≤ (n ^ 2 + 1) * peak n :=
      (free_le_torus n).trans (count_le_mul_peak n)
    have hleR : (freeCount (n - 1) : ℝ) ≤ ((n : ℝ) ^ 2 + 1) * (peak n : ℝ) := by
      exact_mod_cast hle
    have hlog := Real.log_le_log hfpos hleR
    rw [Real.log_mul (by positivity) hp.ne'] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog (sq_nonneg (n : ℝ))
    rw [add_div] at hdiv
    linarith
  · apply Eventually.of_forall
    intro n
    have hp : (0 : ℝ) < peak n := by exact_mod_cast peak_pos n
    have hle : (peak n : ℝ) ≤ freeCount n := by
      exact_mod_cast (peak_le_count n).trans (torus_le_free n)
    exact div_le_div_of_nonneg_right (Real.log_le_log hp hle) (sq_nonneg _)

private theorem root_of_log_limit (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) {s : ℝ}
    (h : Tendsto (fun n : ℕ => Real.log (a n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 s)) :
    Tendsto (rootGrowth a) atTop (𝓝 (Real.exp s)) := by
  convert Real.continuous_exp.continuousAt.tendsto.comp h using 1
  ext n
  simp only [Function.comp_apply]
  rw [rootGrowth, Real.rpow_def_of_pos (by exact_mod_cast ha n), div_eq_mul_inv]

private theorem toroidal_peak_tendsto :
    Tendsto (rootGrowth peak) atTop (𝓝 a247413) := by
  obtain ⟨s, hs, hf⟩ := free_log_limit
  have htlog : Tendsto (fun n : ℕ => Real.log (a063443 n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 s) := by
    simpa only [tiling_free_identity] using shifted_log_limit freeCount hf
  have htpos (n : ℕ) : 0 < a063443 n := by rw [tiling_free_identity]; exact free_pos _
  have ht := root_of_log_limit a063443 htpos htlog
  have hc : a247413 = Real.exp s := ht.limUnder_eq
  rw [hc]
  exact root_of_log_limit peak peak_pos (peak_log_limit hf)

/-- The full published A394697 event, through all integers n at least three. -/
theorem result : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧
    ∀ n : ℕ, N ≤ n → |rootGrowth peak n - a247413| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp toroidal_peak_tendsto ε hε
  refine ⟨max N 3, le_max_right _ _, fun n hn => ?_⟩
  simpa only [Real.dist_eq] using hN n ((le_max_left N 3).trans hn)

#print axioms result

end
end D5.S3.Combinatorics.Graph.ToroidalKingsPeakEntropy
