/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrarily late forward increments realize a logarithmic lower scale. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootSignalCusp
import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder

/-! Recurrence of the actual zero phases transfers the origin cusp into every late tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower (rootCoeff rootCoeff_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit phaseOrbit_cluster_iff)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency exp_mode_norm)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (phaseOrbit_eq_mode)

/-- Read the shifted centered spectrum from a vector of actual occurrence phases. -/
def readSignal (r v : ℝ) (p : ℕ → Circle) : ℝ :=
  (∑' k, rootCoeff r k * (p k : ℂ) * Complex.exp (frequency k * ((v / r : ℝ) : ℂ))).re /
    (1 / 2 - (2 * r)⁻¹)

/-- The shifted spectrum readout is continuous in the phase vector. -/
theorem read_signal_continuous (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (v : ℝ) : Continuous (readSignal r v) := by
  unfold readSignal
  apply Continuous.div_const
  apply Complex.continuous_re.comp
  apply continuous_tsum (fun k => by fun_prop) (actualCoeff_hasSum.summable.norm.mul_left r)
  intro k p
  simpa only [norm_mul, Circle.norm_coe, exp_mode_norm hRH, mul_one] using rootCoeff_bound hr k

/-- On the actual phase orbit the shifted readout recovers the centered spectrum. -/
theorem read_signal_orbit (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (v t : ℝ) : readSignal r v (phaseOrbit t) = rootSignal r (r * t + v) := by
  unfold readSignal rootSignal
  congr 2
  apply tsum_congr
  intro k
  rw [phaseOrbit_eq_mode hRH, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  field_simp

/-- Every strict lower level of the origin symmetric increment recurs arbitrarily late. -/
theorem symmetric_difference_returns (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (h U : ℝ) {b : ℝ} (hb : b < rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0) :
    ∃ t ≥ U, b < rootSignal r (t + h) + rootSignal r (t - h) - 2 * rootSignal r t := by
  let readDifference := fun p : ℕ → Circle =>
    readSignal r h p + readSignal r (-h) p - 2 * readSignal r 0 p
  have hcont : Continuous readDifference :=
    ((read_signal_continuous hRH hr h).add (read_signal_continuous hRH hr (-h))).sub
      (continuous_const.mul (read_signal_continuous hRH hr 0))
  have horbit (t : ℝ) : readDifference (phaseOrbit t) =
      rootSignal r (r * t + h) + rootSignal r (r * t - h) - 2 * rootSignal r (r * t) := by
    simp only [readDifference, read_signal_orbit hRH hr, sub_eq_add_neg, add_zero]
  have hzero : b < readDifference (phaseOrbit 0) := by simpa [horbit] using hb
  have hreturn := (phaseOrbit_cluster_iff (phaseOrbit 0)).2 (subset_closure (mem_range_self _))
  have hlarge := (hreturn.continuousAt_comp hcont.continuousAt).frequently
    (eventually_gt_nhds hzero)
  have hr0 : 0 < r := by linarith
  obtain ⟨t, hvalue, hlate⟩ := (hlarge.and_eventually (eventually_ge_atTop (U / r))).exists
  refine ⟨r * t, ?_, ?_⟩
  · -- The threshold is measured in the original time variable.
    exact (div_le_iff₀ hr0).1 hlate |>.trans_eq (mul_comm _ _)
  · simpa only [Function.comp_apply, horbit] using hvalue

/-- On RH, every sufficiently small shift has a logarithmic-size forward increment
at some start beyond any prescribed bound. -/
theorem root_signal_late_increment_lower (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    ∃ d > 0, ∃ H ∈ Ioo (0 : ℝ) 1, ∀ h : ℝ, 0 < h → h < H → ∀ U : ℝ,
      ∃ u ≥ U, d * h * Real.log (1 / h) ≤ |rootSignal r (u + h) - rootSignal r u| := by
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by linarith)).2 (by linarith)
  obtain ⟨C, hC, hcusp⟩ := root_signal_symmetric_cusp hRH hr
  let B := |Real.log r - 2 * c| + s * C
  let H := min (1 / 2) (min (r / 2) (Real.exp (-(2 * B))))
  have hr0 : 0 < r := by linarith
  have hH0 : 0 < H := lt_min (by norm_num) (lt_min (by positivity) (Real.exp_pos _))
  have hH1 : H < 1 := (min_le_left (1 / 2) _).trans_lt (by norm_num)
  refine ⟨1 / (8 * s), by positivity, H, ⟨hH0, hH1⟩, ?_⟩
  intro h hh hhH U
  have hh1 : h < 1 := hhH.trans hH1
  have hhr : h ≤ r / 2 := hhH.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhexp : h < Real.exp (-(2 * B)) :=
    hhH.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : 2 * B < Real.log (1 / h) := by
    rw [one_div, Real.log_inv]
    linarith [Real.log_lt_log hh hhexp, Real.log_exp (-(2 * B))]
  have hL : 0 < Real.log (1 / h) := Real.log_pos ((lt_div_iff₀ hh).2 (by simpa using hh1))
  let b := h * Real.log (1 / h) / (4 * s)
  have hb : 0 < b := by dsimp [b]; positivity
  have h0 : 2 * b ≤ rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0 := by
    have hi := (abs_le.mp (hcusp h hh hhr)).1
    have hlinear := neg_abs_le (Real.log r - 2 * c)
    have hC' : C * h ^ 2 ≤ C * h := by
      nlinarith [mul_nonneg (mul_nonneg hC.le hh.le) (sub_nonneg.mpr hh1.le)]
    change -(C * h ^ 2) ≤ rootSignal r h + rootSignal r (-h) - 2 * rootSignal r 0 -
      h / s * (Real.log (1 / h) + Real.log r - 2 * c) at hi
    have hscaled := mul_le_mul_of_nonneg_right hi hs.le
    rw [sub_mul, mul_right_comm (h / s), div_mul_cancel₀ _ hs.ne'] at hscaled
    have hbudget := mul_lt_mul_of_pos_left hlog hh
    have hshift := mul_le_mul_of_nonneg_left hlinear hh.le
    have hquadratic := mul_le_mul_of_nonneg_left hC' hs.le
    dsimp [B] at hbudget
    dsimp [b]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 4 * s)).2
    nlinarith only [hscaled, hbudget, hshift, hquadratic]
  obtain ⟨t, ht, hdiff⟩ := symmetric_difference_returns hRH hr h (U + h) (b := b) (by linarith)
  have hsplit :
      b < |rootSignal r (t + h) - rootSignal r t| + |rootSignal r t - rootSignal r (t - h)| := by
    linarith [le_abs_self (rootSignal r (t + h) - rootSignal r t),
      neg_le_abs (rootSignal r t - rootSignal r (t - h))]
  have hsize : 1 / (8 * s) * h * Real.log (1 / h) = b / 2 := by
    dsimp [b]
    field_simp [hs.ne'] <;> norm_num
  rw [hsize]
  by_cases hfirst : b / 2 ≤ |rootSignal r (t + h) - rootSignal r t|
  · exact ⟨t, by linarith, hfirst⟩
  · have hsecond : b / 2 ≤ |rootSignal r t - rootSignal r (t - h)| := by linarith
    exact ⟨t - h, by linarith, by simpa only [sub_add_cancel] using hsecond⟩

#print axioms root_signal_late_increment_lower

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
