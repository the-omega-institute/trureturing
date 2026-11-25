/- GID: D5/S3/Arith/Robin/WeightedTail/SharpTailTransport
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/WeightedTail/SharpTailTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit logarithmic error for normalized weighted-tail transport. -/

import D5.S3.Weil.Mertens.WeightedTailTransport
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! An explicit logarithmic error bound compares the normalized weighted and
unweighted tails of an arbitrary real L1 kernel. -/

namespace D5.S3.Arith.Robin.WeightedTail.SharpTailTransport

open Real Set Filter MeasureTheory
open scoped Topology
open D5.S3.Weil.Mertens.WeightedTailTransport

noncomputable section

/-- A square-root bound on the closed unweighted tail controls the difference
between the two normalized tails, with an explicit logarithmic error. -/
theorem normalized_tail_transport {k : ℝ → ℝ} {x C : ℝ}
    (hx : 2 ≤ x) (hk : IntegrableOn k (Ioi x))
    (hbound : ∀ t ≥ x, |tail k t| ≤ C / sqrt t) :
    |sqrt x * log x * weightedTail k x - sqrt x * tail k x| ≤
      3 * C / log x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs : 0 < sqrt x := sqrt_pos.mpr hx0
  obtain ⟨_, hint, htransport⟩ := transport hx hk
  have hC : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hbound x le_rfl)
    simpa using (le_div_iff₀ hs).mp h
  let d (t : ℝ) : ℝ :=
    1 / (t * sqrt t * log t ^ 2) + 4 / (t * sqrt t * log t ^ 3)
  have hd : ∀ t ∈ Ici x, HasDerivAt (fun t : ℝ => -2 / (sqrt t * log t ^ 2)) (d t) t := by
    intro t ht
    have ht0 : 0 < t := hx0.trans_le ht
    have hs0 : 0 < sqrt t := sqrt_pos.mpr ht0
    have hl0 : 0 < log t := log_pos (by linarith [show x ≤ t from ht])
    have h := (hasDerivAt_const t (-2 : ℝ)).div
      ((Real.hasDerivAt_sqrt ht0.ne').mul ((Real.hasDerivAt_log ht0.ne').pow 2))
      (mul_ne_zero hs0.ne' (pow_ne_zero _ hl0.ne'))
    convert h using 1
    dsimp [d]
    field_simp [ht0.ne', hs0.ne', hl0.ne']
    rw [sq_sqrt ht0.le]
    <;> ring
  have hdnonneg : ∀ t ∈ Ioi x, 0 ≤ d t := by
    intro t ht
    have ht0 : 0 < t := hx0.trans ht
    have hl0 : 0 < log t := log_pos (by linarith [show x < t from ht])
    dsimp [d]
    positivity
  have hlogSq : Tendsto (fun t : ℝ => log t ^ 2) atTop atTop := by
    simpa only [pow_two] using tendsto_log_atTop.atTop_mul_atTop₀ tendsto_log_atTop
  have hlim : Tendsto (fun t : ℝ => -2 / (sqrt t * log t ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_sqrt_atTop.atTop_mul_atTop₀ hlogSq)
  have hdi : IntegrableOn d (Ioi x) := integrableOn_Ioi_deriv_of_nonneg' hd hdnonneg hlim
  have hmass : (∫ t in Ioi x, d t) = 2 / (sqrt x * log x ^ 2) := by
    simpa only [zero_sub, neg_div, neg_neg] using
      integral_Ioi_of_hasDerivAt_of_tendsto' hd hdi hlim
  have hpoint : ∀ t ∈ Ioi x, |density t * tail k t| ≤ C * d t := by
    intro t ht
    have ht0 : 0 < t := hx0.trans ht
    have hs0 : 0 < sqrt t := sqrt_pos.mpr ht0
    have hl0 : 0 < log t := log_pos (by linarith [show x < t from ht])
    have hd0 : 0 ≤ density t := by unfold density; positivity
    rw [abs_mul, abs_of_nonneg hd0]
    calc
      _ ≤ density t * (C / sqrt t) := mul_le_mul_of_nonneg_left (hbound t ht.le) hd0
      _ ≤ C * d t := by
        dsimp [density, d]
        have hden : 0 < t * sqrt t * log t ^ 3 := by positivity
        apply (le_of_mul_le_mul_right ?_ hden)
        field_simp [ht0.ne', hs0.ne', hl0.ne']
        nlinarith
  have hIntegral :
      |∫ t in Ioi x, density t * tail k t| ≤ C * (2 / (sqrt x * log x ^ 2)) := by
    calc
      _ ≤ ∫ t in Ioi x, |density t * tail k t| := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Ioi x))
            (fun t => density t * tail k t)
      _ ≤ ∫ t in Ioi x, C * d t :=
        setIntegral_mono_on hint.abs (hdi.const_mul C) measurableSet_Ioi hpoint
      _ = _ := by rw [integral_const_mul, hmass]
  have hdecomp :
      sqrt x * log x * weightedTail k x - sqrt x * tail k x =
        (sqrt x / log x) * tail k x -
          (sqrt x * log x) * (∫ t in Ioi x, density t * tail k t) := by
    rw [← htransport]
    unfold r
    field_simp [hl.ne']
    ring
  rw [hdecomp]
  calc
    _ ≤ |(sqrt x / log x) * tail k x| +
        |(sqrt x * log x) * (∫ t in Ioi x, density t * tail k t)| := abs_sub _ _
    _ ≤ (sqrt x / log x) * (C / sqrt x) + (sqrt x * log x) * (C * (2 / (sqrt x * log x ^ 2))) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (div_nonneg hs.le hl.le),
        abs_of_nonneg (mul_nonneg hs.le hl.le)]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hbound x le_rfl) (by positivity))
        (mul_le_mul_of_nonneg_left hIntegral (by positivity))
    _ = _ := by
      field_simp [hl.ne', hs.ne']
      ring

#print axioms normalized_tail_transport

end
end D5.S3.Arith.Robin.WeightedTail.SharpTailTransport
