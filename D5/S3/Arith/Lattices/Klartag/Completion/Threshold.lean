/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Threshold
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Threshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.Final
import D5.S3.Arith.Lattices.Klartag.Completion.Assembly

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Threshold

open MeasureTheory
open Metric
open Finset
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling

def n₁ : ℕ := 839

/-- The small-dimension constant at the adopted threshold: `min_{1 ≤ m < 839} Vol(B^{m+1})/m²`. -/
noncomputable def smallConst : ℝ := Final.smallConst n₁

/-- The theorem's constant: `c = min c₀ c₁`, positive. -/
noncomputable def const (c₀ : ℝ) : ℝ := min c₀ smallConst

/-- **`Final.klartag_packing_of_hyps` with the large-`n` branch in `φ` form.**  `Final.Remaining`
is stated through `Assembly.Lemma52`, which is the *lattice*-level packaging; the `Params` route
(`Assembly.exists_phi_of_params`) produces the `φ` directly, so this variant lets it feed the
endgame without repackaging. -/
theorem klartag_packing_of_phi {N₁ : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, N₁ ≤ m →
      ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
        ENNReal.ofReal (c₀ * (m : ℝ) ^ 2) ≤ volume (φ '' Metric.ball 0 1) ∧
        {v ∈ φ '' Metric.ball 0 1 | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0}) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Scaling.klartag_of_volume_ge (min c₀ (Final.smallConst N₁))
    (lt_min hc₀ (Final.smallConst_pos N₁)) ?_
  intro m hm
  by_cases hlarge : N₁ ≤ m
  · obtain ⟨φ, hvol, hint⟩ := H m hlarge
    refine ⟨φ, le_trans (ENNReal.ofReal_le_ofReal ?_) hvol, hint⟩
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · have hid : (LinearMap.id : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (m + 1))) '' Metric.ball 0 1 = Metric.ball 0 1 := by
      ext v; simp
    refine ⟨LinearMap.id, ?_, ?_⟩
    · rw [hid]
      exact Final.small_volume_ge hm (Nat.lt_of_not_le hlarge) (min_le_right _ _)
    · rw [hid]
      exact Final.integerPoints_ball (m + 1)

end D5.S3.Arith.Lattices.Klartag.Completion.Threshold
