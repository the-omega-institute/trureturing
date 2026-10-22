/- GID: D5/S3/Analytic/ExpRatioCM/Extraction
   generality: G
   mirror-B: D5/B/S3/Analytic/ExpRatioCM/Extraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extraction of a distinguished exponential coefficient from scaled derivative values. -/

import D5.S3.Analytic.ExpRatioCM.Series

/-! Coefficient extraction from scaled alternating derivatives. -/

open scoped Topology
open Filter
open D5.S3.Analytic.ExpRatioCM.Defs

namespace D5.S3.Analytic.ExpRatioCM.Extraction

/-!
The analytic estimate used in the coefficient argument has one reusable core:
after the distinguished term has been separated, the remaining geometric tail
tends to zero.  The statement below keeps that estimate independent of the
particular quotient coefficients.  In the application, `hmain` is supplied by
the exponential-series derivative identity and the geometric tail estimate.
-/

/-- A vanishing tail leaves the second exponential coefficient after scaling. -/
theorem extraction_limit {b r : ℕ → ℝ} {h : ℝ → ℝ}
    (hmain : ∀ k : ℕ, 3 ≤ k →
      (49 / 32 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))) =
        b 2 + r k)
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k : ℕ =>
      (49 / 32 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))))
      atTop (𝓝 (b 2)) := by
  have hlim : Tendsto (fun k : ℕ => b 2 + r k) atTop (𝓝 (b 2 + 0)) := by
    simpa using (tendsto_const_nhds.add hr)
  have hlim' : Tendsto (fun k : ℕ => b 2 + r k) atTop (𝓝 (b 2)) := by
    simpa using hlim
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop 3] with k hk
  exact (hmain k hk).symm

/-- A negative extracted coefficient rules out complete monotonicity. -/
theorem not_completelyMonotone_of_extraction
    {h : ℝ → ℝ} {b : ℕ → ℝ}
    (hlim : Tendsto (fun k : ℕ =>
      (49 / 32 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))))
      atTop (𝓝 (b 2)))
    (hb : b 2 < 0) :
    ¬ CompletelyMonotoneOn h := by
  intro hcm
  have hnonneg : ∀ᶠ k : ℕ in atTop,
      0 ≤ (49 / 32 : ℝ) ^ k *
        ((-1 : ℝ) ^ k * iteratedDeriv k h (k * Real.log (7 / 4))) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have ht : 0 < (k : ℝ) * Real.log (7 / 4) := by
      have hlog : 0 < Real.log (7 / 4) := Real.log_pos (by norm_num)
      positivity
    have hd := hcm.2 k ((k : ℝ) * Real.log (7 / 4)) ht
    exact mul_nonneg (by positivity) hd
  have hmem : b 2 ∈ Set.Ici 0 := isClosed_Ici.mem_of_tendsto hlim hnonneg
  exact (not_le_of_gt hb) hmem

end D5.S3.Analytic.ExpRatioCM.Extraction
