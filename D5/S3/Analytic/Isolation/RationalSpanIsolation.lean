/- GID: D5/S3/Analytic/Isolation/RationalSpanIsolation
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/RationalSpanIsolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed rational-span levels of a nonconstant real-analytic family are isolated. -/

import Mathlib.Analysis.Analytic.Order

/- Provenance: thin honest wrapper over pinned mathlib's isolated-zero theorem
   `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`, applied after subtracting
   the fixed rational linear combination. -/

namespace D5.S3.Analytic.Isolation.RationalSpanIsolation

/-- For fixed rational coefficients over a finite real family, a level set of
a real-analytic function is codiscrete within a connected parameter interval
as soon as the function misses that level at one point. -/
theorem rational_span_level_set_codiscrete
    {F : ℝ → ℝ} {P : Set ℝ}
    (hF : AnalyticOnNhd ℝ F P) (hP : IsConnected P)
    {ι : Type*} [Fintype ι] (q : ι → ℚ) (b : ι → ℝ)
    {x : ℝ} (hx : x ∈ P)
    (hne : F x ≠ ∑ i, (q i : ℝ) * b i) :
    F ⁻¹' {∑ i, (q i : ℝ) * b i}ᶜ ∈ Filter.codiscreteWithin P := by
  let c : ℝ := ∑ i, (q i : ℝ) * b i
  have hFc : AnalyticOnNhd ℝ (fun y ↦ F y - c) P :=
    hF.sub analyticOnNhd_const
  have hne_zero : F x - c ≠ 0 := sub_ne_zero.mpr hne
  have hcodiscrete :=
    hFc.preimage_zero_mem_codiscreteWithin hne_zero hx hP
  convert hcodiscrete using 1
  ext y
  constructor
  · exact sub_ne_zero.mpr
  · exact sub_ne_zero.mp

end D5.S3.Analytic.Isolation.RationalSpanIsolation
