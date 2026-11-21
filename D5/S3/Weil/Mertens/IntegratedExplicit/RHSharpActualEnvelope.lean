/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under RH the full zero mass bounds G and recurs at arbitrarily late natural arguments. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Tactic

/-! The complete phase series and the exact arithmetic residual give both real-axis control
and arbitrarily late natural recurrence under RH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology BigOperators
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Arith.Robin.CompleteMertensPeak (U)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

def G (y : ℝ) : ℝ := Real.exp (-y / 2) * U (Real.exp y)

/-- Under RH, each actual zero occurrence has real part one half. -/
lemma on_line (hRH : RiemannHypothesis) (k : ℕ) :
    (actualZero k).re = 1 / 2 := by
  simpa only [actualZero, D5.S3.Weil.Convention.criticalAbscissa] using
    zeroData_zero_on_critical_line_of_rh hRH actualData (actualOccurrenceEquiv k).1

/-- Under RH, each actual zero coefficient is a positive real reciprocal. -/
lemma coeff_real (hRH : RiemannHypothesis) (k : ℕ) :
    actualCoeff k = ((1 / (1 / 4 + (actualZero k).im ^ 2) : ℝ) : ℂ) := by
  have hd : actualZero k * (1 - actualZero k) =
      ((1 / 4 + (actualZero k).im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
        on_line hRH k] <;> ring
  simp only [actualCoeff, hd, Complex.ofReal_div, Complex.ofReal_one]

/-- Under RH, the sum of the norms of all actual zero coefficients is the first Li mass. -/
lemma coeff_norm_hasSum (hRH : RiemannHypothesis) :
    HasSum (fun k : ℕ => ‖actualCoeff k‖) firstLiMass := by
  have hn (k : ℕ) : ‖actualCoeff k‖ = (actualCoeff k).re := by
    rw [coeff_real hRH k]
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    exact abs_of_pos (one_div_pos.mpr (by positivity))
  simpa only [hn, Complex.ofReal_re] using Complex.hasSum_re actualCoeff_hasSum

private def normalizedH (y : ℝ) : ℂ := (Real.exp (-y / 2) : ℂ) * actualH y
private def phase : ℕ → Circle := fun k => Circle.exp (actualZero k).im
private def phaseSum (z : ℕ → Circle) : ℂ := ∑' k : ℕ, actualCoeff k * (z k : ℂ)

private lemma phaseSum_continuous (hRH : RiemannHypothesis) : Continuous phaseSum := by
  apply continuous_tsum (fun k => by fun_prop) (coeff_norm_hasSum hRH).summable
  intro k z
  simp only [norm_mul, Circle.norm_coe, mul_one, le_refl]

private lemma phaseSum_one : phaseSum 1 = (firstLiMass : ℂ) := by
  simpa [phaseSum] using actualCoeff_hasSum.tsum_eq

lemma normalizedH_bound (hRH : RiemannHypothesis) (y : ℝ) :
    ‖normalizedH y‖ ≤ firstLiMass := by
  have ht (k : ℕ) :
      ‖actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
        ‖actualCoeff k‖ * Real.exp (y / 2) := by
    simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, on_line hRH k]
    rw [show y * (1 / 2) = y / 2 by ring]
  have hh : ‖actualH y‖ ≤ firstLiMass * Real.exp (y / 2) :=
    tsum_of_norm_bounded ((coeff_norm_hasSum hRH).mul_right _) ht
  calc
    ‖normalizedH y‖ = Real.exp (-y / 2) * ‖actualH y‖ := by
      unfold normalizedH
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-y / 2) * (firstLiMass * Real.exp (y / 2)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
    _ = firstLiMass := by
      calc
        _ = firstLiMass * (Real.exp (-y / 2) * Real.exp (y / 2)) := by ring
        _ = firstLiMass := by
          rw [← Real.exp_add, show -y / 2 + y / 2 = 0 by ring, Real.exp_zero, mul_one]

private lemma phaseSum_pow (hRH : RiemannHypothesis) (n : ℕ) :
    phaseSum (phase ^ n) = normalizedH (n : ℝ) := by
  rw [phaseSum, normalizedH, actualH, ← tsum_mul_left]
  congr 1
  funext k
  have hp : (((phase ^ n) k : Circle) : ℂ) =
      Complex.exp (((n : ℝ) * (actualZero k).im : ℝ) * Complex.I) := by
    simp only [Pi.pow_apply, phase, Circle.coe_pow, Circle.coe_exp]
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  have he : Complex.exp (((n : ℝ) * (actualZero k).im : ℝ) * Complex.I) =
      (Real.exp (-(n : ℝ) / 2) : ℂ) *
        Complex.exp (((n : ℝ) : ℂ) * actualZero k) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, on_line hRH k]
    ring
  rw [hp, he]
  ring

private def residual (y : ℝ) : ℝ :=
  Real.exp (-y / 2) * (Real.log (2 * Real.pi) - trivialT y)

private lemma G_split {y : ℝ} (hy : 0 < y) :
    G y = (normalizedH y).re + residual y := by
  have h := congrArg Complex.re (actual_integrated_explicit_formula hy)
  simp only [Complex.ofReal_re] at h
  simp only [G, normalizedH, residual, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [h]
  ring

private lemma G_split_nonneg {y : ℝ} (hy : 0 ≤ y) :
    G y = (normalizedH y).re + residual y := by
  have hG : Continuous G := by
    unfold G
    exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 2))).mul U_exp_continuous
  have hH : Continuous (fun t => (normalizedH t).re) := by
    unfold normalizedH
    exact Complex.continuous_re.comp ((by fun_prop :
      Continuous (fun t : ℝ => (Real.exp (-t / 2) : ℂ))).mul actualH_continuous)
  have hR : ContinuousOn residual (Ici 0) := by
    unfold residual
    exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 2))).continuousOn.mul
      (continuousOn_const.sub trivialT_continuousOn)
  have h : EqOn G (fun t => (normalizedH t).re + residual t) (Ioi 0) :=
    fun _ ht => G_split ht
  exact h.of_subset_closure hG.continuousOn (hH.continuousOn.add hR)
    Ioi_subset_Ici_self (by rw [closure_Ioi]) hy

private lemma abs_residual_lt {y : ℝ} (hy : 0 ≤ y) :
    |residual y| < Real.exp (-y / 2) * Real.log (2 * Real.pi) := by
  have hlog : Real.log 2 ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have hsign : 0 < Real.log (2 * Real.pi) - trivialT y := by
    linarith [trivialT_le_mass hy, Real.log_two_gt_d9]
  have hpos : 0 < trivialT y := by
    have hterm : 0 < trivialCoeff 0 * Real.exp (-(2 * ((↑(0 : ℕ) : ℝ) + 1)) * y) := by
      unfold trivialCoeff
      positivity
    exact hterm.trans_le ((trivialT_summable hy).le_tsum 0
      (fun n _ => mul_nonneg (trivialCoeff_nonneg n) (Real.exp_nonneg _)))
  rw [residual, abs_of_pos (mul_pos (Real.exp_pos _) hsign)]
  exact mul_lt_mul_of_pos_left (sub_lt_self _ hpos) (Real.exp_pos _)

/-- The normalized arithmetic remainder and real zero series differ by strictly less
than `exp (-y / 2) * log (2 * π)` on the closed nonnegative half-axis. -/
lemma abs_G_sub_normalized_actualH_le {y : ℝ} (hy : 0 ≤ y) :
    |G y - Real.exp (-y / 2) * (actualH y).re| <
      Real.exp (-y / 2) * Real.log (2 * Real.pi) := by
  have hsplit := G_split_nonneg hy
  rw [normalizedH, Complex.re_ofReal_mul] at hsplit
  rw [hsplit, add_sub_cancel_left]
  exact abs_residual_lt hy

private lemma residual_zero : Tendsto residual atTop (𝓝 0) := by
  have he : Tendsto (fun y : ℝ => Real.exp (-y / 2)) atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2))).congr
        (fun y => by simp [div_eq_mul_inv, neg_mul])
  apply squeeze_zero_norm' (a := fun y =>
    Real.exp (-y / 2) * Real.log (2 * Real.pi)) ?_
    (by simpa using he.mul_const (Real.log (2 * Real.pi)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simpa only [Real.norm_eq_abs] using (abs_residual_lt hy).le

/-- The normalized integrated prime term differs from the complete real zero
series by a vanishing explicit-formula residual. -/
lemma G_sub_normalized_actualH_tendsto_zero :
    Tendsto (fun y : ℝ => G y - Real.exp (-y / 2) * (actualH y).re) atTop (𝓝 0) := by
  apply residual_zero.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  have hsplit := G_split_nonneg hy
  simp only [normalizedH, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hsplit
  simp only [hsplit, add_sub_cancel_left]

/-- Full-axis eventual control and recurrence of the complete actual occurrence series. -/
theorem actual_G_control (hRH : RiemannHypothesis) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ y : ℝ in atTop, |G y| < firstLiMass + epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ n : ℕ, Y ≤ (n : ℝ) ∧ |G (n : ℝ) - firstLiMass| < epsilon) := by
  have hres : Tendsto (fun y : ℝ => |residual y|) atTop (𝓝 0) := by
    simpa only [abs_zero] using residual_zero.abs
  constructor
  · intro epsilon he
    filter_upwards [hres.eventually_lt_const he,
      eventually_ge_atTop (0 : ℝ)] with y hr hy
    rw [G_split_nonneg hy]
    calc
      _ ≤ |(normalizedH y).re| + |residual y| := abs_add_le _ _
      _ ≤ ‖normalizedH y‖ + |residual y| :=
        add_le_add (Complex.abs_re_le_norm _) le_rfl
      _ < firstLiMass + epsilon := add_lt_add_of_le_of_lt (normalizedH_bound hRH y) hr
  · intro epsilon he Y
    have hcluster : MapClusterPt (firstLiMass : ℂ) atTop
        (fun n : ℕ => phaseSum (phase ^ n)) := by
      simpa only [phaseSum_one, Function.comp_def] using
        (mapClusterPt_one_atTop_pow phase).continuousAt_comp
          (phaseSum_continuous hRH).continuousAt
    have hfreq : ∃ᶠ n : ℕ in atTop,
        ‖phaseSum (phase ^ n) - (firstLiMass : ℂ)‖ < epsilon / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using
        hcluster.frequently (Metric.ball_mem_nhds _ (by positivity : 0 < epsilon / 2))
    have hr : ∀ᶠ n : ℕ in atTop, |residual (n : ℝ)| < epsilon / 2 :=
      tendsto_natCast_atTop_atTop.eventually
        (hres.eventually_lt_const (by positivity : 0 < epsilon / 2))
    have hY : ∀ᶠ n : ℕ in atTop, Y ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Y)
    obtain ⟨n, hn, hrn, hYn⟩ := (hfreq.and_eventually (hr.and hY)).exists
    refine ⟨n, hYn, ?_⟩
    rw [phaseSum_pow hRH] at hn
    rw [G_split_nonneg (Nat.cast_nonneg n)]
    have hre : |(normalizedH (n : ℝ)).re - firstLiMass| < epsilon / 2 := by
      have := (Complex.abs_re_le_norm
        (normalizedH (n : ℝ) - (firstLiMass : ℂ))).trans_lt hn
      simpa only [Complex.sub_re, Complex.ofReal_re] using this
    calc
      _ = |((normalizedH (n : ℝ)).re - firstLiMass) + residual (n : ℝ)| := by ring_nf
      _ ≤ |(normalizedH (n : ℝ)).re - firstLiMass| + |residual (n : ℝ)| := abs_add_le _ _
      _ < epsilon := by linarith

end D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
