/- SOURCE CANDIDATE ONLY. No native or registration claim.
   This is the reusable signed integral step in section479: it retains the
   entire nonoscillatory envelope and the entire complement of the interval.
   It does not assert that the actual zeta primitive has a peak. -/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set

namespace D5.S3.Analytic.GaussianSignedLocalization

/-- Signed localization with an envelope. All integrability obligations are
explicit and independent of the claimed inequality. No lower bound on H is
needed in J, and no part of the complement is discarded. -/
theorem signed_localization_bound (H K v b : ℝ → ℝ) (J : Set ℝ)
    (hJ : MeasurableSet J)
    (hv : ∀ y, 0 ≤ v y) (hK : ∀ y, |K y| ≤ v y)
    (hb : ∀ y ∈ J, 0 ≤ b y) (hH : ∀ y ∈ J, H y ≤ b y)
    (hHK : Integrable (fun y => H y * K y))
    (hHv : Integrable (fun y => H y * v y))
    (hbv : IntegrableOn (fun y => 2 * (b y * v y)) J)
    (hout : IntegrableOn (fun y => 2 * (|H y| * v y)) Jᶜ) :
    (∫ y : ℝ, H y * K y) ≤
      (∫ y in J, 2 * (b y * v y)) +
        (∫ y in Jᶜ, 2 * (|H y| * v y)) + |∫ y : ℝ, H y * v y| := by
  have hi := ((integrable_indicator_iff hJ).mpr hbv).add
    ((integrable_indicator_iff hJ.compl).mpr hout)
  have hpoint (y : ℝ) : H y * K y ≤
      J.indicator (fun x => 2 * (b x * v x)) y +
        Jᶜ.indicator (fun x => 2 * (|H x| * v x)) y - H y * v y := by
    obtain ⟨hKm, hKp⟩ := abs_le.mp (hK y)
    by_cases hy : y ∈ J
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_notMem (show y ∉ Jᶜ from fun h => h hy), add_zero]
      have hpos : 0 ≤ K y + v y := by linarith
      have hmul := mul_le_mul_of_nonneg_right (hH y hy) hpos
      have hbudget := mul_le_mul_of_nonneg_left hKp (hb y hy)
      nlinarith
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_mem
        (show y ∈ Jᶜ from hy), zero_add]
      have hh : H y ≤ |H y| := le_abs_self _
      have hpos : 0 ≤ K y + v y := by linarith
      have hmul := mul_le_mul_of_nonneg_right hh hpos
      have hbudget := mul_le_mul_of_nonneg_left hKp (abs_nonneg (H y))
      nlinarith
  have hbound := integral_mono hHK (hi.sub hHv) hpoint
  have hbound' : (∫ y : ℝ, H y * K y) ≤
      ∫ y : ℝ, (J.indicator (fun x => 2 * (b x * v x)) y +
        Jᶜ.indicator (fun x => 2 * (|H x| * v x)) y) - H y * v y := by
    simpa only [Pi.sub_apply, Pi.add_apply] using hbound
  have hsub : (∫ y : ℝ, (J.indicator (fun x => 2 * (b x * v x)) y +
      Jᶜ.indicator (fun x => 2 * (|H x| * v x)) y) - H y * v y) =
      (∫ y : ℝ, J.indicator (fun x => 2 * (b x * v x)) y +
        Jᶜ.indicator (fun x => 2 * (|H x| * v x)) y) -
        ∫ y : ℝ, H y * v y := by
    simpa only [Pi.sub_apply, Pi.add_apply] using integral_sub hi hHv
  have hadd : (∫ y : ℝ, J.indicator (fun x => 2 * (b x * v x)) y +
      Jᶜ.indicator (fun x => 2 * (|H x| * v x)) y) =
      (∫ y in J, 2 * (b y * v y)) +
        ∫ y in Jᶜ, 2 * (|H y| * v y) := by
    simpa only [Pi.add_apply, integral_indicator hJ, integral_indicator hJ.compl] using
      integral_add ((integrable_indicator_iff hJ).mpr hbv)
        ((integrable_indicator_iff hJ.compl).mpr hout)
  calc
    _ ≤ (∫ y : ℝ, J.indicator (fun x => 2 * (b x * v x)) y +
        Jᶜ.indicator (fun x => 2 * (|H x| * v x)) y) -
        ∫ y : ℝ, H y * v y := hbound'.trans_eq hsub
    _ ≤ _ := by
      rw [hadd]
      have habs := neg_le_abs (∫ y : ℝ, H y * v y)
      simpa only [sub_eq_add_neg] using
        add_le_add_right habs
          ((∫ y in J, 2 * (b y * v y)) + ∫ y in Jᶜ, 2 * (|H y| * v y))

end D5.S3.Analytic.GaussianSignedLocalization
