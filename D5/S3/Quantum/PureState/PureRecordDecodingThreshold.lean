/- GID: D5/S3/Quantum/PureState/PureRecordDecodingThreshold
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PureRecordDecodingThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The one-label success curve has the quarter-rate finite-scale crossover. -/

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PureRecordDecodingThreshold

open Filter
open scoped Topology

/-- The scalar success curve, evaluated at the squared overlap for equiprobable pure states. -/
noncomputable def singleSuccess (x : ℝ) : ℝ := (1 + Real.sqrt (1 - x)) / 2

private theorem singleSuccess_pos (x : ℝ) : 0 < singleSuccess x := by
  unfold singleSuccess
  positivity

private theorem log_success_slope :
    Tendsto (fun x : ℝ => Real.log (singleSuccess x) / x) (𝓝[≠] 0) (𝓝 (-(1 / 4))) := by
  have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
    change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) - id) (-1) 0
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ))
  have hroot : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x)) (-(1 / 2)) 0 := by
    convert hsub.sqrt (by norm_num) using 1 <;> norm_num
  have hs : HasDerivAt singleSuccess (-(1 / 4)) 0 := by
    unfold singleSuccess
    convert ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hroot).div_const 2 using 1 <;>
      norm_num
  have hz : singleSuccess 0 = 1 := by norm_num [singleSuccess]
  have hlog : HasDerivAt (fun x => Real.log (singleSuccess x)) (-(1 / 4)) 0 := by
    convert hs.log (singleSuccess_pos 0).ne' using 1
    norm_num [singleSuccess]
  simpa only [zero_add, hz, Real.log_one, sub_zero, smul_eq_mul, div_eq_inv_mul] using
    hlog.tendsto_slope_zero

/-- The scalar success powers converge at finite scale for inputs tending to zero
that are eventually nonzero. -/
theorem joint_success_crossover (overlapSq : ℕ → ℝ) (copies : ℕ → ℕ) (scale : ℝ)
    (hzero : Tendsto overlapSq atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop, overlapSq n ≠ 0)
    (hscale : Tendsto (fun n => (copies n : ℝ) * overlapSq n) atTop (𝓝 scale)) :
    Tendsto (fun n => singleSuccess (overlapSq n) ^ copies n) atTop
      (𝓝 (Real.exp (-scale / 4))) := by
  have hnear : Tendsto overlapSq atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, by simpa using hne⟩
  have hlog := log_success_slope.comp hnear
  have hexp : Tendsto (fun n => (copies n : ℝ) * Real.log (singleSuccess (overlapSq n)))
      atTop (𝓝 (-scale / 4)) := by
    have hprod := hscale.mul hlog
    have hlimit : scale * (-(1 / 4) : ℝ) = -scale / 4 := by ring
    rw [hlimit] at hprod
    apply hprod.congr'
    filter_upwards [hne] with n hn
    change (copies n : ℝ) * overlapSq n *
      (Real.log (singleSuccess (overlapSq n)) / overlapSq n) = _
    field_simp [hn]
  have hpow := Real.continuous_exp.continuousAt.tendsto.comp hexp
  apply hpow.congr'
  exact Eventually.of_forall fun n => by
    change Real.exp ((copies n : ℝ) * Real.log (singleSuccess (overlapSq n))) = _
    rw [Real.exp_nat_mul, Real.exp_log (singleSuccess_pos _)]

end PureRecordDecodingThreshold
