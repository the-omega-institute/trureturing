/- GID: D5/S3/Analytic/BesselRedheffer/FirstZero
   generality: G
   mirror-B: D5/B/S3/Analytic/BesselRedheffer/FirstZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts, mathlib/module/Mathlib.Topology.Order.IntermediateValue, mathlib/module/Mathlib.Topology.Order.Monotone]
   utility: none
   digest: A weighted energy bound, existence, and positivity of the first normalized Bessel zero. -/

import D5.S3.Analytic.BesselRedheffer.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone

open Set MeasureTheory Filter Topology
open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Series

set_option maxHeartbeats 800000

namespace D5.S3.Analytic.BesselRedheffer.FirstZero

private lemma exists_zero_of_nonpos {ν x : ℝ} (hν : -1 < ν) (hx : 0 ≤ x)
    (hfx : nbessel ν x ≤ 0) : ∃ r, 0 < r ∧ r ≤ x ∧ nbessel ν r = 0 := by
  have hm : (0 : ℝ) ∈ Icc (nbessel ν x) (nbessel ν 0) := by
    rw [nbessel_zero]
    exact ⟨hfx, zero_le_one⟩
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc' hx (continuous_nbessel hν).continuousOn hm
  refine ⟨r, ?_, hr.2, hfr⟩
  rcases hr.1.eq_or_lt with he | hp
  · subst r
    rw [nbessel_zero] at hfr
    norm_num at hfr
  · exact hp

/-- The normalized series stays positive before its first positive zero. -/
theorem nbessel_pos_of_lt {ν x : ℝ} (hν : -1 < ν) (hx : 0 ≤ x)
    (hxj : x < firstZero ν) : 0 < nbessel ν x := by
  by_contra hn
  obtain ⟨r, hr, hrx, hfr⟩ := exists_zero_of_nonpos hν hx (le_of_not_gt hn)
  have hbelow : BddBelow {r : ℝ | 0 < r ∧ nbessel ν r = 0} := ⟨0, fun r hr => hr.1.le⟩
  have hjr : firstZero ν ≤ r := csInf_le hbelow ⟨hr, hfr⟩
  linarith

end D5.S3.Analytic.BesselRedheffer.FirstZero
