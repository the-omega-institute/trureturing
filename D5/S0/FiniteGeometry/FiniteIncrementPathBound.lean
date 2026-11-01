/- GID: D5/S0/FiniteGeometry/FiniteIncrementPathBound
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/FiniteIncrementPathBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform boundedness of all admissible finite paths with a fixed finite increment set. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace D5.S0.FiniteGeometry.FiniteIncrementPathBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finitely many increment directions give one neighborhood preserving every
strictly positive projection at the center. -/
private lemma local_radius (V : Finset E) (u : E) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ s v : E, ‖s - u‖ < δ → v ∈ V →
        ⟪s, v⟫_ℝ ≤ 0 → ⟪u, v⟫_ℝ ≤ 0 := by
  classical
  induction V using Finset.induction_on with
  | empty => exact ⟨1 / 2, by norm_num, le_rfl, by simp⟩
  | @insert v V hv ih =>
    obtain ⟨δ, hδ, hδhalf, hlocal⟩ := ih
    by_cases huv : ⟪u, v⟫_ℝ ≤ 0
    · refine ⟨δ, hδ, hδhalf, ?_⟩
      intro s z hs hz hsz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact huv
      · exact hlocal s z hs hz hsz
    · have hp : 0 < ⟪u, v⟫_ℝ := lt_of_not_ge huv
      let ε := ⟪u, v⟫_ℝ / (2 * (‖v‖ + 1))
      have hε : 0 < ε := by dsimp [ε]; positivity
      refine ⟨min δ ε, lt_min hδ hε, (min_le_left _ _).trans hδhalf, ?_⟩
      intro s z hs hz hsz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have hdist : ‖u - s‖ < ε := by
          rw [norm_sub_rev]
          exact hs.trans_le (min_le_right _ _)
        have hcs := (le_abs_self ⟪u - s, v⟫_ℝ).trans
          (abs_real_inner_le_norm (u - s) v)
        rw [inner_sub_left] at hcs
        have he : ε * (2 * (‖v‖ + 1)) = ⟪u, v⟫_ℝ := by
          dsimp [ε]
          exact div_mul_cancel₀ _ (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hdist.le (norm_nonneg v)
        nlinarith [norm_nonneg v]
      · exact hlocal s z (hs.trans_le (min_le_left _ _)) hz hsz

end D5.S0.FiniteGeometry.FiniteIncrementPathBound
