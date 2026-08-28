/- GID: D5/S3/Weil/Scattering/ScatteringResonanceLines
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/ScatteringResonanceLines
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Critical zeta zeros map to the scattering quarter lines. -/

import D5.S3.Weil.ZeroSum

namespace D5.S3.Weil.Scattering.ScatteringResonanceLines

open D5.S3.Weil.ZeroSum

/-!
Search receipt (2026-08-28): `D5.S3.Weil.ZeroSum.IsNontrivialZero` is the canonical
critical-strip zero predicate used here. No frozen D5 theorem states either affine line equivalence.
-/

/-- The strip-native Riemann hypothesis is equivalent both to every parameter `ρ / 2` lying on
the resonance line `re s = 1 / 4` and to every reflected parameter `1 - ρ / 2` lying on the
antiresonance line `re s = 3 / 4`. -/
theorem scattering_resonance_lines :
    ((∀ rho : ℂ, IsNontrivialZero rho → rho.re = 1 / 2) ↔
      (∀ rho : ℂ, IsNontrivialZero rho → (rho / 2).re = 1 / 4)) ∧
    ((∀ rho : ℂ, IsNontrivialZero rho → rho.re = 1 / 2) ↔
      (∀ rho : ℂ, IsNontrivialZero rho → (1 - rho / 2).re = 3 / 4)) := by
  constructor
  · constructor
    · intro h rho hrho
      have := h rho hrho
      norm_num at ⊢
      linarith
    · intro h rho hrho
      have hline := h rho hrho
      norm_num at hline
      linarith
  · constructor
    · intro h rho hrho
      have := h rho hrho
      norm_num at ⊢
      linarith
    · intro h rho hrho
      have hline := h rho hrho
      norm_num at hline
      linarith

end D5.S3.Weil.Scattering.ScatteringResonanceLines
