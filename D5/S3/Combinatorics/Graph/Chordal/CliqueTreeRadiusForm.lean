/- GID: D5/S3/Combinatorics/Graph/Chordal/CliqueTreeRadiusForm
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed form of the clique-tree extension radius recurrence. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential

compile_only_with_mathlib

/-! Omega original.

The closed form of the clique-tree extension recurrence initialized at one.
-/

namespace SimpleGraph

theorem cliqueTreeRadius_closed_form {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    cliqueTreeRadius m 1 h =
      ((m : ℝ) - 1) - ((m : ℝ) - 2) * (((m : ℝ) - 1) / m) ^ h := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  let t := ((m : ℝ) - 1) / m
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hm0.le
  have ht1 : t ≤ 1 := (div_le_iff₀ hm0).mpr (by linarith)
  have ht : 1 - 1 / (m : ℝ) = t := by dsimp [t]; field_simp
  induction h with
  | zero => norm_num [cliqueTreeRadius]
  | succ h ih =>
    rw [cliqueTreeRadius, ih]
    change max (max ((m : ℝ) - 1 - ((m : ℝ) - 2) * t ^ h) 1)
      ((1 - 1 / (m : ℝ)) * (1 + ((m : ℝ) - 1 - ((m : ℝ) - 2) * t ^ h))) =
      (m : ℝ) - 1 - ((m : ℝ) - 2) * t ^ (h + 1)
    have he : (1 - 1 / (m : ℝ)) * (1 + ((m : ℝ) - 1 - ((m : ℝ) - 2) * t ^ h)) =
        (m : ℝ) - 1 - ((m : ℝ) - 2) * t ^ (h + 1) := by
      rw [ht, pow_succ]
      have htm : t * (m : ℝ) = (m : ℝ) - 1 := div_mul_cancel₀ _ hm0.ne'
      calc
        _ = t * (m : ℝ) - ((m : ℝ) - 2) * (t ^ h * t) := by ring
        _ = _ := by rw [htm]
    have hp : t ^ h ≤ 1 := pow_le_one₀ ht0 ht1
    have hmon : t ^ (h + 1) ≤ t ^ h := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg ht0 _) ht1
    rw [he, max_eq_right]
    apply max_le
    · linarith only [mul_le_mul_of_nonneg_left hmon (show 0 ≤ (m : ℝ) - 2 by linarith)]
    · have hpow : t ^ (h + 1) ≤ 1 := hmon.trans hp
      have := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (m : ℝ) - 2 by linarith)
      linarith

end SimpleGraph
