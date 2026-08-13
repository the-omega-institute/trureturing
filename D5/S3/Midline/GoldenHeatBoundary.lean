/- GID: D5/S3/Midline/GoldenHeatBoundary
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boundary divergence of the golden heat spectrum and its flat L2 midline. -/

import Mathlib
import D5.S3.Midline.GoldenHeatSpectrum
import D5.S3.Midline.UniversalHeatTrace

/- Provenance: Native proof over pinned mathlib. -/
/- SEARCH RECEIPT (2026-08-14): D5 declarations searched for the boundary
   spectrum claim (miss; this file is the new result); pinned mathlib searched
   for Nat.Primes.not_summable_one_div, Nat.Primes.summable_rpow,
   Real.rpow_def_of_pos, Real.rpow_neg_one, and Summable.comp_injective (hits);
   no admissible third-party result was used. -/

namespace D5.S3.Midline.GoldenHeatBoundary

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Midline.UniversalHeatTrace

noncomputable section

private theorem golden_boundary_term (p : Nat.Primes) :
    Real.exp (-(1 / Real.goldenRatio ^ 2) * goldenSpectrum (p, 0)) =
      (p : Real) ^ (-1 : Real) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast p.prop.pos)]
  simp only [goldenSpectrum, Nat.zero_add, o5_beta_power_law.1]
  congr 1
  field_simp [ne_of_gt Real.goldenRatio_pos]

/-- The `v = 1` prime layer is the divergent boundary subfamily. -/
theorem golden_heat_boundary_divergent :
    BoundaryDivergentAbscissa goldenSpectrum (1 / Real.goldenRatio ^ 2) := by
  refine ⟨golden_heat_abscissa, ?_⟩
  intro hsum
  have hsub : Summable (fun p : Nat.Primes =>
      Real.exp (-(1 / Real.goldenRatio ^ 2) * goldenSpectrum (p, 0))) :=
    hsum.comp_injective (fun a b hab => congrArg Prod.fst hab)
  have hrpow : Summable (fun p : Nat.Primes => (p : Real) ^ (-1 : Real)) := by
    exact (summable_congr (fun p => golden_boundary_term p)).mp hsub
  exact Nat.Primes.not_summable_one_div (by
    simpa only [Real.rpow_neg_one, one_div] using hrpow)

theorem golden_heat_l2_iff :
    ∀ s : Complex,
      Memℓp (heatCoefficient goldenSpectrum s) 2 ↔
        1 / (2 * Real.goldenRatio ^ 2) < s.re := by
  intro s
  have h := (heat_coefficient_mem_iff_of_boundary_divergent
    goldenSpectrum (1 / Real.goldenRatio ^ 2)
    golden_heat_boundary_divergent s)
  have hhalf : (1 / Real.goldenRatio ^ 2) / 2 =
      1 / (2 * Real.goldenRatio ^ 2) := by
    field_simp [ne_of_gt Real.goldenRatio_pos]
  rw [hhalf] at h
  exact h

end

end D5.S3.Midline.GoldenHeatBoundary
