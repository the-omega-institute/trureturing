/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Final
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Final
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.Assembly
import D5.S3.Arith.Lattices.Klartag.Construction.Scaling

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Final

open MeasureTheory
open Metric
open Finset
open D5.S3.Arith.Lattices.Klartag

/-- Every coordinate of a Euclidean vector is bounded by its norm. -/
theorem abs_coord_le_norm {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) : |v i| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖v.ofLp i‖ ^ 2 ≤ ∑ j, ‖v.ofLp j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖v.ofLp j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h1 : |v.ofLp i| = Real.sqrt (‖v.ofLp i‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs]
  rw [h1]
  exact Real.sqrt_le_sqrt hle

/-- **The unit ball has no non-zero integer point** — the open cube `(−1,1)^N` contains it, and an
integer of absolute value `< 1` is `0`. -/
theorem integerPoints_ball (N : ℕ) :
    {v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1 |
      ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, mem_ball, dist_zero_right]
  constructor
  · rintro ⟨hnorm, hint⟩
    ext i
    obtain ⟨k, hk⟩ := hint i
    have hlt : |v i| < 1 := lt_of_le_of_lt (abs_coord_le_norm v i) hnorm
    rw [← hk] at hlt
    have hk0 : k = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (by omega)
      linarith
    have : v i = 0 := by rw [← hk, hk0]; norm_num
    simpa using this
  · rintro rfl
    exact ⟨by simp, fun i => ⟨0, by simp⟩⟩

/-- `Vol(B^N)` as a real number. -/
noncomputable def ballVol (N : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal

theorem ballVol_pos (N : ℕ) : 0 < ballVol N := by
  refine ENNReal.toReal_pos (ne_of_gt ?_) (measure_ball_lt_top).ne
  exact measure_ball_pos _ _ zero_lt_one

theorem ofReal_ballVol (N : ℕ) :
    ENNReal.ofReal (ballVol N) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  ENNReal.ofReal_toReal (measure_ball_lt_top).ne

/-- `c₁ = min_{1 ≤ m < n₁} Vol(B^{m+1}) / m²`, a minimum over a finite set. -/
noncomputable def smallConst (n₁ : ℕ) : ℝ :=
  if h : (Finset.Ico 1 n₁).Nonempty then
    (Finset.Ico 1 n₁).inf' h (fun m => ballVol (m + 1) / (m : ℝ) ^ 2)
  else 1

theorem smallConst_pos (n₁ : ℕ) : 0 < smallConst n₁ := by
  rw [smallConst]
  split
  · rename_i h
    rw [Finset.lt_inf'_iff]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.1 hm).1
    have : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      positivity
    exact div_pos (ballVol_pos _) this
  · norm_num

theorem smallConst_le {n₁ m : ℕ} (h1 : 1 ≤ m) (h2 : m < n₁) :
    smallConst n₁ ≤ ballVol (m + 1) / (m : ℝ) ^ 2 := by
  have hmem : m ∈ Finset.Ico 1 n₁ := Finset.mem_Ico.2 ⟨h1, h2⟩
  have hne : (Finset.Ico 1 n₁).Nonempty := ⟨m, hmem⟩
  rw [smallConst, dif_pos hne]
  exact Finset.inf'_le _ hmem

/-- The small-dimension bound in the form `klartag_of_volume_ge` consumes. -/
theorem small_volume_ge {n₁ m : ℕ} (h1 : 1 ≤ m) (h2 : m < n₁) {c : ℝ}
    (hc : c ≤ smallConst n₁) :
    ENNReal.ofReal (c * (m : ℝ) ^ 2)
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
  have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
  have hmsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hle : c * (m : ℝ) ^ 2 ≤ ballVol (m + 1) := by
    have := le_trans hc (smallConst_le h1 h2)
    rw [le_div_iff₀ hmsq] at this
    exact this
  rw [← ofReal_ballVol (m + 1)]
  exact ENNReal.ofReal_le_ofReal hle

end D5.S3.Arith.Lattices.Klartag.Completion.Final
