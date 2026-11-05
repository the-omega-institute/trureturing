/- GID: D5/S3/Analytic/GaussianSignedLocalization
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussianSignedLocalization
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Signed localization with the full envelope debit and exact measurable complement. -/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set

namespace D5.S3.Analytic.GaussianSignedLocalization

/-- Signed localization before the absolute-value relaxation. Only the central
budget and exterior majorant need restricted integrability. The full signed
envelope integral is subtracted, with neither sign nor complement discarded.
Consumed by OriginalPositiveUPeak.full_E_upper_of_central_bound. -/
theorem signed_localization_debit
    (f k v B : ℝ → ℝ) (J : Set ℝ) (hJ : MeasurableSet J)
    (hk : ∀ y, |k y| ≤ v y)
    (hB : ∀ y ∈ J, 0 ≤ B y) (hfB : ∀ y ∈ J, f y ≤ B y)
    (hfk : Integrable (fun y => f y * k y))
    (hfv : Integrable (fun y => f y * v y))
    (hBv : IntegrableOn (fun y => B y * v y) J)
    (hav : IntegrableOn (fun y => |f y| * v y) Jᶜ) :
    (∫ y : ℝ, f y * k y) ≤
      2 * (∫ y in J, B y * v y) +
        2 * (∫ y in Jᶜ, |f y| * v y) - ∫ y : ℝ, f y * v y := by
  have hcentral : Integrable (J.indicator (fun y => 2 * (B y * v y))) :=
    (integrable_indicator_iff hJ).mpr (hBv.const_mul 2)
  have hexterior : Integrable (Jᶜ.indicator (fun y => 2 * (|f y| * v y))) :=
    (integrable_indicator_iff hJ.compl).mpr (hav.const_mul 2)
  have hpoint (y : ℝ) : f y * k y ≤
      J.indicator (fun x => 2 * (B x * v x)) y +
        Jᶜ.indicator (fun x => 2 * (|f x| * v x)) y - f y * v y := by
    obtain ⟨hkm, hkp⟩ := abs_le.mp (hk y)
    have hplus : 0 ≤ k y + v y := by linarith
    by_cases hy : y ∈ J
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_notMem (show y ∉ Jᶜ from fun h => h hy), add_zero]
      have hmul := mul_le_mul_of_nonneg_right (hfB y hy) hplus
      have hbudget := mul_le_mul_of_nonneg_left hkp (hB y hy)
      nlinarith
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_mem (show y ∈ Jᶜ from hy), zero_add]
      have hmul := mul_le_mul_of_nonneg_right (le_abs_self (f y)) hplus
      have hbudget := mul_le_mul_of_nonneg_left hkp (abs_nonneg (f y))
      nlinarith
  have hle := integral_mono hfk ((hcentral.add hexterior).sub hfv) hpoint
  have hle' : (∫ x : ℝ, f x * k x) ≤
      ∫ x : ℝ,
        (J.indicator (fun y => 2 * (B y * v y)) x +
            Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x) - f x * v x := by
    simpa only [Pi.add_apply, Pi.sub_apply] using hle
  have hsub :
      (∫ x : ℝ,
          J.indicator (fun y => 2 * (B y * v y)) x +
            Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x - f x * v x) =
        (∫ x : ℝ,
          J.indicator (fun y => 2 * (B y * v y)) x +
            Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x) -
          ∫ x : ℝ, f x * v x := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      (integral_sub (hcentral.add hexterior) hfv)
  calc
    (∫ x : ℝ, f x * k x) ≤
        ∫ x : ℝ,
          (J.indicator (fun y => 2 * (B y * v y)) x +
              Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x) - f x * v x := hle'
    _ = (2 * (∫ y in J, B y * v y) +
          2 * (∫ y in Jᶜ, |f y| * v y)) - ∫ y : ℝ, f y * v y := by
      rw [hsub, integral_add hcentral hexterior,
        integral_indicator hJ, integral_indicator hJ.compl,
        integral_const_mul, integral_const_mul]

end D5.S3.Analytic.GaussianSignedLocalization
