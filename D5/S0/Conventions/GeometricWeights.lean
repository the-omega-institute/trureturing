/- GID: D5/S0/Conventions/GeometricWeights
   generality: I
   mirror-B: D5/B/S0/Conventions/GeometricWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No nonzero rational rescaling of geometric weights matches all singleton W weights. -/

import D5.S0.Conventions.WDigits
import Mathlib.Tactic.Linarith

namespace D5.S0.Conventions.GeometricWeights

/-- Geometric weights cannot reproduce all singleton Zeckendorf weights up to nonzero scale. -/
theorem no_geometric_weights_match_zeckendorf_singletons :
    ¬ ∃ (w₁ Λ c : ℚ), c ≠ 0 ∧ ∀ k : ℕ, w₁ * Λ ^ k = c * (Nat.fib (k + 2) : ℚ) := by
  rintro ⟨w₁, Λ, c, hc, h⟩
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  norm_num [Nat.fib] at h₀ h₁ h₂
  rcases lt_or_gt_of_ne hc with hc | hc <;> nlinarith

end D5.S0.Conventions.GeometricWeights
