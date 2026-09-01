/- GID: D5/S3/Weil/ZetaLinear/OfflineZeroSpectralQuotient
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/OfflineZeroSpectralQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute the reflection-quotient coordinate of an offline-zero parameter. -/

import D5.S3.Weil.ZetaLinear.OfflineZeroCharacter
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom has empty `coverage_gids` and no formalization receipt. Repository
     searches for spectral/reflection quotient coordinates and products with
     `1 - s` found `functionalReflection` and the existing offline-zero
     character, but no declaration of the quotient coordinate or its formula.
     This module reuses their common complex parameter `rho` and reflection.
   * Pinned Mathlib supplies `mul_one_sub`, `Complex.ext`, the real and imaginary
     part formulas for complex multiplication, and `ring`; it has no declaration
     packaging the displayed offline-zero coordinate identity.
   * The Lean skill's local semantic search and searches of the installed
     admissible third-party packages returned no matching declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaLinear.OfflineZeroSpectralQuotient

open D5.S3.Weil.Convention
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening

/-- The reflection-quotient coordinate `lambda(s) = s(1 - s)`. -/
def spectralQuotientCoordinate (s : ℂ) : ℂ :=
  s * functionalReflection s

/-- Formula (1126.3): if `rho = 1/2 + delta + i gamma`, its reflection-quotient
coordinate has real part `1/4 + gamma^2 - delta^2` and imaginary part
`-2 delta gamma`. -/
theorem offline_zero_spectral_quotient_coordinate
    (rho : ℂ) (delta gamma : ℝ)
    (hRho :
      rho =
        ((criticalAbscissa + delta : ℝ) : ℂ) +
          Complex.I * (gamma : ℂ)) :
    spectralQuotientCoordinate rho =
      ((1 / 4 + gamma ^ 2 - delta ^ 2 : ℝ) : ℂ) -
        Complex.I * ((2 * delta * gamma : ℝ) : ℂ) := by
  rw [hRho]
  apply Complex.ext <;>
    simp [spectralQuotientCoordinate, functionalReflection, pow_two,
      criticalAbscissa] <;>
    ring

/-- The coordinate definition is realized by the concrete parameters
`delta = gamma = 1`. -/
theorem exists_offline_zero_spectral_quotient_realization :
    ∃ rho : ℂ,
      spectralQuotientCoordinate rho =
        (1 / 4 : ℂ) - Complex.I * 2 := by
  refine ⟨((3 / 2 : ℝ) : ℂ) + Complex.I, ?_⟩
  simpa [criticalAbscissa] using
    offline_zero_spectral_quotient_coordinate
      (((3 / 2 : ℝ) : ℂ) + Complex.I) 1 1 (by
        norm_num [criticalAbscissa])

#print axioms offline_zero_spectral_quotient_coordinate
#print axioms exists_offline_zero_spectral_quotient_realization

end D5.S3.Weil.ZetaLinear.OfflineZeroSpectralQuotient
