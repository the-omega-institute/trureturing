/- GID: D5/S3/Estimation/CorrelationWeightSpectralBound
   generality: G
   mirror-B: D5/B/S3/Estimation/CorrelationWeightSpectralBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two leading spectral values force a strict centered second-moment bound. -/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Estimation.CorrelationWeightSpectralBound

private lemma two_point_energy {n : ℕ} (hn : 3 ≤ n) (μ : Fin n → ℝ)
    (hsum : ∑ j, μ j = 0) (i j : Fin n) (hij : i ≠ j) :
    (n : ℝ) * (μ i + μ j) ^ 2 ≤
      2 * ((n : ℝ) - 2) * ∑ k, μ k ^ 2 := by
  sorry

private lemma top_pair_of_weights {n : ℕ} (hn : 3 ≤ n) (μ w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (i : Fin n)
    (htop : ∀ j, μ j ≤ μ i) (hhalf : w i < 1 / 2) :
    ∃ j, j ≠ i ∧ 2 * (∑ k, μ k * w k) ≤ μ i + μ j := by
  sorry

/-- A top spectral weight below one half forces a larger centered second moment. -/
theorem centered_energy_strict {n : ℕ} (hn : 3 ≤ n) (c σ : ℝ) (hc : 0 < c)
    (μ w : Fin n → ℝ) (hμ : ∑ j, μ j = 0)
    (henergy : ∑ j, μ j ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (c ^ 2 + σ ^ 2))
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (hrayleigh : ∑ j, μ j * w j = ((n : ℝ) - 1) * c)
    (i : Fin n) (htop : ∀ j, μ j ≤ μ i) (hhalf : w i < 1 / 2) :
    c ^ 2 < σ ^ 2 := by
  obtain ⟨j, hji, hpair⟩ := top_pair_of_weights hn μ w hw hsum i htop hhalf
  have hbound := two_point_energy hn μ hμ i j hji.symm
  sorry

end D5.S3.Estimation.CorrelationWeightSpectralBound
