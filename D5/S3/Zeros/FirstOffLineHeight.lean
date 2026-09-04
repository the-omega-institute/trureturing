/- GID: D5/S3/Zeros/FirstOffLineHeight
   generality: G
   mirror-B: D5/B/S3/Zeros/FirstOffLineHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero entire function with strip-bounded off-line zeros has a first positive off-line height. -/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Lemmas

open Complex Set

namespace D5.S3.Zeros.FirstOffLineHeight

/-- Positive imaginary parts at which `F` has a zero away from `midline`. -/
def positiveOffLineHeights (F : Complex → Complex) (midline : Real) : Set Real :=
  {t | 0 < t ∧ ∃ z, F z = 0 ∧ z.re ≠ midline ∧ z.im = t}

/-- A nonzero entire function whose zeros stay in a fixed vertical strip has a least positive
off-line zero height whenever such a zero exists. -/
theorem first_off_line_height_exists (F : Complex → Complex) (midline bound : Real)
    (hEntire : ∀ z, AnalyticAt Complex F z) (nonzeroPoint : Complex)
    (hNonzero : F nonzeroPoint ≠ 0) (hBound : 0 ≤ bound)
    (hStrip : ∀ z, F z = 0 → |z.re| ≤ bound)
    (hOffLine : (positiveOffLineHeights F midline).Nonempty) :
    ∃ T, T ∈ positiveOffLineHeights F midline ∧
      ∀ t, t ∈ positiveOffLineHeights F midline → T ≤ t := by
  obtain ⟨t0, ht0⟩ := hOffLine
  have ht0pos : 0 < t0 := ht0.1
  let K : Set Complex := Metric.closedBall 0 (bound + t0)
  let Z : Set Complex := K \ F ⁻¹' ({0} : Set Complex)ᶜ
  let lowHeights : Set Real := positiveOffLineHeights F midline ∩ Set.Iic t0

  have hAnalytic : AnalyticOnNhd Complex F Set.univ := fun z _ => hEntire z
  have hCodiscrete : F ⁻¹' ({0} : Set Complex)ᶜ ∈ Filter.codiscrete Complex :=
    hAnalytic.preimage_zero_mem_codiscrete hNonzero
  have hCodiscreteK : F ⁻¹' ({0} : Set Complex)ᶜ ∈ Filter.codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ K) hCodiscrete
  have hZFinite : Z.Finite := by
    change (K \ F ⁻¹' ({0} : Set Complex)ᶜ).Finite
    have hKCompact : IsCompact K := by
      simpa [K] using isCompact_closedBall (0 : Complex) (bound + t0)
    exact hKCompact.finite_sdiff_of_mem_codiscreteWithin hCodiscreteK

  have hLowFinite : lowHeights.Finite := by
    apply (hZFinite.image Complex.im).subset
    intro t ht
    rcases ht.1 with ⟨htpos, z, hzZero, -, hzIm⟩
    have hzNorm : norm z ≤ bound + t0 := by
      calc
        norm z ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ = |z.re| + t := by rw [hzIm, abs_of_pos htpos]
        _ ≤ bound + t0 := add_le_add (hStrip z hzZero) ht.2
    refine ⟨z, ?_, hzIm⟩
    constructor
    · simpa [K, Metric.mem_closedBall, dist_zero_right] using hzNorm
    · simp [hzZero]

  have ht0Low : t0 ∈ lowHeights := by
    refine ⟨ht0, ?_⟩
    simpa using (le_rfl : t0 ≤ t0)
  have hLowNonempty : lowHeights.Nonempty := ⟨t0, ht0Low⟩
  obtain ⟨T, hTLow, hTLeast⟩ :=
    Set.exists_min_image lowHeights id hLowFinite hLowNonempty
  refine ⟨T, hTLow.1, ?_⟩
  intro t ht
  by_cases htLe : t ≤ t0
  · exact hTLeast t ⟨ht, htLe⟩
  · exact (hTLeast t0 ht0Low).trans (le_of_lt (lt_of_not_ge htLe))

end D5.S3.Zeros.FirstOffLineHeight
