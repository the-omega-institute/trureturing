/- GID: D5/S3/DivergenceSupport/PathRatioBound
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/PathRatioBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The path-integrated output/input divergence ratio equals the pointwise-contraction-ratio weighted average and is bounded by the supremum of those pointwise ratios (SDPI path reading). -/

import Mathlib

namespace D5.S3.DivergenceSupport.PathRatioBound

open MeasureTheory Set
open scoped Interval

/-- Input and output squared path speeds for a channel along a mixture path. -/
structure PathSpeedData where
  inputSq : ℝ → ℝ
  outputSq : ℝ → ℝ

/-- The path weight `(1-s) * ||Delta||^2` from the source claim. -/
def pathWeight (d : PathSpeedData) (s : ℝ) : ℝ :=
  (1 - s) * d.inputSq s

/-- The pointwise contraction ratio. -/
noncomputable def pointwiseRatio (d : PathSpeedData) (s : ℝ) : ℝ :=
  d.outputSq s / d.inputSq s

/-- The source path divergence. -/
noncomputable def sourcePath (d : PathSpeedData) : ℝ :=
  ∫ s in (0 : ℝ)..1, pathWeight d s

/-- The channel-output path divergence. -/
noncomputable def targetPath (d : PathSpeedData) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s) * d.outputSq s

/-- A concrete upper bound for all pointwise contraction ratios on the path. -/
def BoundsPathRatio (d : PathSpeedData) (eta : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, pointwiseRatio d s ≤ eta

/-- The supremum of the pointwise ratios along the mixture path. -/
noncomputable def pathSup (d : PathSpeedData) : ℝ :=
  sSup (pointwiseRatio d '' Icc (0 : ℝ) 1)

/-- The output/input divergence ratio is the path-ratio weighted average and
is bounded by every upper bound on the pointwise ratios. -/
private theorem path_ratio_weighted_average_and_bound_of_bound
    (d : PathSpeedData) (eta : ℝ)
    (hinput : ∀ s ∈ Icc (0 : ℝ) 1, 0 < d.inputSq s)
    (hsource : IntervalIntegrable (pathWeight d) volume 0 1)
    (hratio : IntervalIntegrable (fun s => pointwiseRatio d s * pathWeight d s)
      volume 0 1)
    (hbound : BoundsPathRatio d eta) :
    targetPath d = ∫ s in (0 : ℝ)..1, pointwiseRatio d s * pathWeight d s ∧
      targetPath d ≤ eta * sourcePath d := by
  have hpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (1 - s) * d.outputSq s = pointwiseRatio d s * pathWeight d s := by
    rw [pointwiseRatio, pathWeight]
    field_simp [ne_of_gt (hinput s hs)]
  constructor
  · rw [targetPath]
    apply intervalIntegral.integral_congr
    intro s hs
    exact hpoint s (by simpa [uIcc_of_le zero_le_one] using hs)
  · rw [targetPath]
    calc
      (∫ s in (0 : ℝ)..1, (1 - s) * d.outputSq s) =
          ∫ s in (0 : ℝ)..1, pointwiseRatio d s * pathWeight d s := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact hpoint s (by simpa [uIcc_of_le zero_le_one] using hs)
      _ ≤ ∫ s in (0 : ℝ)..1, eta * pathWeight d s := by
        apply intervalIntegral.integral_mono_on zero_le_one hratio (hsource.const_mul eta)
        intro s hs
        have hweight : 0 ≤ pathWeight d s := by
          exact mul_nonneg (by linarith [hs.2]) (le_of_lt (hinput s hs))
        exact mul_le_mul_of_nonneg_right (hbound s hs) hweight
      _ = eta * sourcePath d := by
        rw [sourcePath, intervalIntegral.integral_const_mul]

/-- The true path contraction is the pointwise-ratio weighted average and is
therefore at most the supremum of those pointwise ratios. -/
theorem path_ratio_weighted_average_and_bound
    (d : PathSpeedData)
    (hinput : ∀ s ∈ Icc (0 : ℝ) 1, 0 < d.inputSq s)
    (hsource : IntervalIntegrable (pathWeight d) volume 0 1)
    (hratio : IntervalIntegrable (fun s => pointwiseRatio d s * pathWeight d s)
      volume 0 1)
    (hsourcePos : 0 < sourcePath d)
    (hbounded : BddAbove (pointwiseRatio d '' Icc (0 : ℝ) 1)) :
    targetPath d = ∫ s in (0 : ℝ)..1, pointwiseRatio d s * pathWeight d s ∧
      targetPath d ≤ pathSup d * sourcePath d ∧
      targetPath d / sourcePath d =
        ∫ s in (0 : ℝ)..1, pointwiseRatio d s * (pathWeight d s / sourcePath d) := by
  have hsup : BoundsPathRatio d (pathSup d) := by
    intro s hs
    exact le_csSup hbounded ⟨s, hs, rfl⟩
  have hmain := path_ratio_weighted_average_and_bound_of_bound d (pathSup d)
    hinput hsource hratio hsup
  refine ⟨hmain.1, hmain.2, ?_⟩
  calc
    targetPath d / sourcePath d =
        (∫ s in (0 : ℝ)..1, pointwiseRatio d s * pathWeight d s) / sourcePath d := by
      rw [hmain.1]
    _ = ∫ s in (0 : ℝ)..1,
          (pointwiseRatio d s * pathWeight d s) / sourcePath d := by
      rw [intervalIntegral.integral_div]
    _ = ∫ s in (0 : ℝ)..1,
          pointwiseRatio d s * (pathWeight d s / sourcePath d) := by
      apply intervalIntegral.integral_congr
      intro s _
      field_simp [ne_of_gt hsourcePos]

end D5.S3.DivergenceSupport.PathRatioBound
