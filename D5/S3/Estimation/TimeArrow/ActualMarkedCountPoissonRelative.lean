/- GID: D5/S3/Estimation/TimeArrow/ActualMarkedCountPoissonRelative
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ActualMarkedCountPoissonRelative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative Poisson transfer for one or two native marked departure rows. -/

import D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative

open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative

/-- Uniform relative control at integral observation scale. -/
theorem actual_marked_count_poisson_relative (κ C₀ : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hC : 1 ≤ C₀) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L k : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → (k = 1 ∨ k = 2) →
        ∀ (S : Support M q) (m : Fin k → Fin M), Function.Injective m →
          ∀ (np nm : Fin k → ℕ),
            (∀ j, (np j : ℝ) ≤ C₀ * L ∧ (nm j : ℝ) ≤ C₀ * L) →
            ∀ e : Experiment,
              let T := 2 * M * L
              let μp := fun j => (L : ℝ) * (1 + b r S (.inl (m j))) / 2
              let μm := fun j => (L : ℝ) * (1 - b r S (.inl (m j))) / 2
              let P := ∑ o : Obs M T e,
                if ∀ j, count e o (m j) 1 = np j ∧ count e o (m j) (-1) = nm j
                then probability r e S o else 0
              let Q := ∏ j, (Real.exp (-μp j) * (μp j) ^ np j / (np j).factorial) *
                (Real.exp (-μm j) * (μm j) ^ nm j / (nm j).factorial)
              |P / Q - 1| ≤ A * (L : ℝ) ^ (k + 1) / M := by
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ :=
    D5.S3.Estimation.TimeArrow.ArbitraryMarkedCountPoissonRelative.arbitrary_marked_count_poisson_relative
      κ C₀ hκ hκ1 hC
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L k r hMM hq hqm hr hrκ hcκ hL hLη hk S m hm np nm hn e
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hscale : (((2 * M * L : ℕ) : ℝ) / (2 * M)) = (L : ℝ) := by
    push_cast
    field_simp
  have hh := h M q (2 * M * L) k r hMM hq hqm hr hrκ hcκ
  rw [hscale] at hh
  exact hh (by exact_mod_cast hL) hLη hk S m hm np nm hn e

#print axioms actual_marked_count_poisson_relative
end D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative
