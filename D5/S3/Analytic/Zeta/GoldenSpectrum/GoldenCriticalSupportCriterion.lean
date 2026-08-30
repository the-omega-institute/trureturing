/- GID: D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalSupportCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalSupportCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A spectral set lies on the critical line exactly when its golden exponential image lies on the unit circle, and reflection-stable sets are only pairwise charge-balanced without this stronger pointwise condition. -/

import D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalCoordinate
import Mathlib

/- Library-search audit trail (2026-08-30):
   * Repository searches for a set-level golden unit-circle criterion and the
     distinction between pairwise reflection balance and pointwise criticality
     found no exact D5 owner.
   * `ToroidalInnerThresholdIdentity` and Cayley-support proposals use different
     coordinate systems and are not duplicated.
   * The proof reuses the exact pointwise criterion from
     `GoldenCriticalCoordinate`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalSupportCriterion

open Set
open D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalCoordinate

/-- Every point in a spectral set lies on the critical line. -/
def IsCriticalSupport (zeros : Set ℂ) : Prop :=
  ∀ s ∈ zeros, s.re = (1 / 2 : ℝ)

/-- Every point in a spectral set has unit golden radial charge. -/
def IsGoldenUnitarySupport (zeros : Set ℂ) : Prop :=
  ∀ s ∈ zeros, ‖goldenCriticalCoordinate s‖ = 1

/-- The critical-line statement and golden unit-circle statement are exactly
equivalent for any spectral set. -/
theorem critical_support_iff_golden_unitary_support (zeros : Set ℂ) :
    IsCriticalSupport zeros ↔ IsGoldenUnitarySupport zeros := by
  constructor
  · intro hCritical s hs
    exact (norm_golden_critical_coordinate_eq_one_iff s).2
      (hCritical s hs)
  · intro hUnitary s hs
    exact (norm_golden_critical_coordinate_eq_one_iff s).1
      (hUnitary s hs)

/-- Reflection stability only guarantees that every observed point has a
reciprocal-charge partner. -/
theorem reflection_stable_support_pair_balance
    {zeros : Set ℂ}
    (hReflection : ∀ s ∈ zeros, criticalReflection s ∈ zeros) :
    ∀ s ∈ zeros,
      goldenRadialCharge s *
        goldenRadialCharge (criticalReflection s) = 1 := by
  intro s _
  exact golden_reflection_pair_charge_product s

/-- A two-point reflected orbit can be globally charge-balanced while failing
the pointwise unitary condition. -/
theorem balanced_reflection_orbit_need_not_be_critical :
    let s : ℂ := (3 / 4 : ℝ)
    let zeros : Set ℂ := {s, criticalReflection s}
    (∀ z ∈ zeros,
      goldenRadialCharge z *
        goldenRadialCharge (criticalReflection z) = 1) ∧
      ¬ IsCriticalSupport zeros := by
  dsimp
  constructor
  · intro z hz
    exact golden_reflection_pair_charge_product z
  · intro hCritical
    have hs : ((3 / 4 : ℝ) : ℂ) ∈
        ({((3 / 4 : ℝ) : ℂ),
          criticalReflection ((3 / 4 : ℝ) : ℂ)} : Set ℂ) := by
      simp
    have hReal := hCritical ((3 / 4 : ℝ) : ℂ) hs
    norm_num at hReal

/-- Pointwise golden unitarity gives pairwise balance as a consequence. -/
theorem unitary_support_implies_pair_balance
    {zeros : Set ℂ} (hUnitary : IsGoldenUnitarySupport zeros)
    {s : ℂ} (hs : s ∈ zeros)
    (hReflected : criticalReflection s ∈ zeros) :
    ‖goldenCriticalCoordinate s‖ *
      ‖goldenCriticalCoordinate (criticalReflection s)‖ = 1 := by
  rw [hUnitary s hs, hUnitary (criticalReflection s) hReflected]
  norm_num

/-- The singleton at the critical center is an inhabited unitary support. -/
example :
    IsGoldenUnitarySupport ({((1 / 2 : ℝ) : ℂ)} : Set ℂ) := by
  intro s hs
  simp only [Set.mem_singleton_iff] at hs
  subst s
  exact (norm_golden_critical_coordinate_eq_one_iff _).2 (by simp)

#print axioms critical_support_iff_golden_unitary_support
#print axioms reflection_stable_support_pair_balance
#print axioms balanced_reflection_orbit_need_not_be_critical
#print axioms unitary_support_implies_pair_balance

end D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalSupportCriterion
