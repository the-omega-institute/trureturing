/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero-normalized original Gaussian determinant-period identity on the unit disk. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianDeterminant
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianTraceBilinear
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

/-! Analytic identities for the original signed Gaussian operator and its literal cutoffs. -/

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology
open Set Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity

open OriginalGaussianMatrix OriginalGaussianResolvent
open OriginalGaussianDeterminant
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

/- Zero normalization is a consequence of the ACTUAL section logarithms. -/
private lemma finiteSection_zero (N : ℕ) : finiteSection N 0 = 0 := by
  ext i j
  change matrixEntry 0 (i.val + 1) (j.val + 1) = 0
  have hpos : 0 < (i.val + 1) + (j.val + 1) := by omega
  simp only [matrixEntry, zero_pow (Nat.ne_of_gt hpos), mul_zero, Matrix.zero_apply]

private lemma finiteLog_zero (N : ℕ) : finiteLog N 0 = 0 := by
  have hterm (k : ℕ) :
      Matrix.trace (finiteSection N 0 ^ (2 * (k + 1))) / (k + 1 : ℂ) = 0 := by
    rw [finiteSection_zero, zero_pow (by omega : 2 * (k + 1) ≠ 0)]
    simp
  simp only [finiteLog, hterm, tsum_zero, neg_zero]

/-- The actual infinite-cycle logarithm is zero at the zero operator. -/
theorem gaussianLogDet_zero : gaussianLogDet 0 = 0 := by
  have h : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (gaussianLogDet 0)) := by
    simpa only [finiteLog_zero] using finiteLog_tendsto (z := 0) (by norm_num)
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The normalization comes from the original cutoff limit. -/
theorem gaussianDet_zero : gaussianDet 0 = 1 := by
  rw [gaussianDet, gaussianLogDet_zero, Complex.exp_zero]

/- F is the real part of the EXISTING complex period. Its missing imaginary
   part vanishes term by term by conjugation; no replacement series is defined. -/
private lemma period_ofReal (r : ℝ) :
    D5.S3.Analytic.OriginalHalfBinomialPeriod.period (r : ℂ) = (F r : ℂ) := by
  change D5.S3.Analytic.OriginalHalfBinomialPeriod.period (r : ℂ) =
    ((D5.S3.Analytic.OriginalHalfBinomialPeriod.period (r : ℂ)).re : ℂ)
  symm
  apply Complex.conj_eq_iff_re.mp
  rw [D5.S3.Analytic.OriginalHalfBinomialPeriod.period, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [halfBinomial_eq_signed_centralWeight]
  simp

private lemma F_zero : F 0 = 1 := by
  have hp : D5.S3.Analytic.OriginalHalfBinomialPeriod.period 0 = 1 := by
    rw [D5.S3.Analytic.OriginalHalfBinomialPeriod.period, tsum_eq_single 0]
    · norm_num [halfBinomial]
    · intro n hn
      simp only [zero_pow hn, mul_zero]
  change (D5.S3.Analytic.OriginalHalfBinomialPeriod.period (0 : ℂ)).re = 1
  rw [hp]
  rfl

private lemma F_differentiableAt {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    DifferentiableAt ℝ F r := by
  have hz : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  have hd := (D5.S3.Analytic.OriginalHalfBinomialPeriod.picard_fuchs hz).1.hasDerivAt
  exact hd.real_of_complex.differentiableAt

private lemma realLogPeriod_hasDerivAt {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t : ℝ =>
      ((Real.log (F t) + (1 / 4 : ℝ) * Real.log (1 - t) : ℝ) : ℂ))
      ((deriv F r / F r - 1 / (4 * (1 - r)) : ℝ) : ℂ) r := by
  have hF : F r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.le hr1))
  have hb : (1 : ℝ) - r ≠ 0 := by linarith
  have h₁ := (F_differentiableAt hr.le hr1).hasDerivAt.log hF
  have h₂ := (((hasDerivAt_id r).const_sub 1).log hb).const_mul (1 / 4 : ℝ)
  have hd : HasDerivAt
      (fun t : ℝ => Real.log (F t) + (1 / 4 : ℝ) * Real.log (1 - t))
      (deriv F r / F r - 1 / (4 * (1 - r))) r := by
    convert h₁.fun_add h₂ using 1 <;>
      first | rfl | (simp only [id_eq]; field_simp [hb, hF] <;> ring)
  exact hd.ofReal_comp

private lemma radialLog_continuousOn :
    ContinuousOn (fun t : ℝ => gaussianLogDet (Real.sqrt t : ℂ)) (Ico 0 1) := by
  have hc : Continuous (fun t : ℝ => (Real.sqrt t : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_sqrt
  exact gaussianLogDet_differentiableOn.continuousOn.comp hc.continuousOn
    (fun t ht => radial_norm_lt_one ht.2)

private lemma realLogPeriod_continuousOn :
    ContinuousOn (fun t : ℝ =>
      ((Real.log (F t) + (1 / 4 : ℝ) * Real.log (1 - t) : ℝ) : ℂ)) (Ico 0 1) := by
  intro r hr
  have hF : F r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (F_ge_one hr.1 hr.2))
  have hb : (1 : ℝ) - r ≠ 0 := by linarith [hr.2]
  have hcF := (Real.continuousAt_log hF).comp (F_differentiableAt hr.1 hr.2).continuousAt
  have hcb : ContinuousAt (fun t : ℝ => Real.log (1 - t)) r :=
    (Real.continuousAt_log hb).comp (continuous_const.sub continuous_id).continuousAt
  have hc : ContinuousAt
      (fun t : ℝ => Real.log (F t) + (1 / 4 : ℝ) * Real.log (1 - t)) r :=
    hcF.add (continuousAt_const.mul hcb)
  exact (Complex.continuous_ofReal.continuousAt.comp hc).continuousWithinAt

/-- Integration with the constant FIXED at zero. The temporary interior value
    below is eliminated using continuity and gaussianLogDet_zero, not assumed. -/
theorem gaussianLogDet_real_normalization {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    gaussianLogDet (Real.sqrt r : ℂ) =
      ((Real.log (F r) + (1 / 4 : ℝ) * Real.log (1 - r) : ℝ) : ℂ) := by
  let Δ : ℝ → ℂ := fun t => gaussianLogDet (Real.sqrt t : ℂ) -
    ((Real.log (F t) + (1 / 4 : ℝ) * Real.log (1 - t) : ℝ) : ℂ)
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Δ 0 t := by
    intro t ht
    simpa only [Δ, sub_self] using
      (OriginalGaussianTraceBilinear.gaussianLogDet_hasDerivAt_period ht.1 ht.2).fun_sub
        (realLogPeriod_hasDerivAt ht.1 ht.2)
  have hc : ContinuousOn Δ (Ico (0 : ℝ) 1) :=
    radialLog_continuousOn.sub realLogPeriod_continuousOn
  have heq : EqOn Δ (fun _ => Δ (1 / 2)) (Ioo (0 : ℝ) 1) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 1).isPreconnected
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) ht (by constructor <;> norm_num)
  have hext : EqOn Δ (fun _ => Δ (1 / 2)) (Ico (0 : ℝ) 1) := by
    apply heq.of_subset_closure hc continuousOn_const
    · intro t ht
      exact ⟨ht.1.le, ht.2⟩
    · rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact Ico_subset_Icc_self
  have hz : Δ 0 = 0 := by
    dsimp only [Δ]
    rw [Real.sqrt_zero, Complex.ofReal_zero, gaussianLogDet_zero, F_zero]
    norm_num
  have he : Δ r = 0 := (hext ⟨hr, hr1⟩).trans ((hext ⟨le_rfl, zero_lt_one⟩).symm.trans hz)
  exact sub_eq_zero.mp he

/-- The normalized identity for the actual original infinite-cycle determinant,
    INCLUDING r=0. F is the existing real restriction of the literal period. -/
theorem gaussianDet_real_period_identity {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    gaussianDet (Real.sqrt r : ℂ) =
      ((Real.rpow (1 - r) (1 / 4 : ℝ) * F r : ℝ) : ℂ) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [Real.sqrt_zero, Complex.ofReal_zero, gaussianDet_zero, sub_zero,
      Real.rpow_eq_pow, Real.one_rpow, F_zero, mul_one, Complex.ofReal_one]
  have hb : 0 < (1 : ℝ) - r := by linarith
  have hF : 0 < F r := lt_of_lt_of_le zero_lt_one (F_ge_one hr hr1)
  rw [gaussianDet, gaussianLogDet_real_normalization hr hr1, ← Complex.ofReal_exp]
  congr 1
  rw [Real.exp_add, Real.exp_log hF, Real.rpow_eq_pow, Real.rpow_def_of_pos hb]
  rw [mul_comm (1 / 4 : ℝ) (Real.log (1 - r)), mul_comm (F r)]

private lemma norm_sq_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖z ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num : (2 : ℕ) ≠ 0)

/- This pays the principal-log branch globally, including all complex phases. -/
private lemma one_sub_sq_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 - z ^ 2).re := by
  have he : (z ^ 2).re < 1 := (Complex.re_le_norm _).trans_lt (norm_sq_lt_one hz)
  simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr he

private lemma one_sub_sq_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ^ 2 ∈ Complex.slitPlane :=
  Or.inl (one_sub_sq_re_pos hz)

private lemma periodProduct_differentiableOn :
    DifferentiableOn ℂ (fun z : ℂ =>
      Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - z ^ 2)) *
        D5.S3.Analytic.OriginalHalfBinomialPeriod.period (z ^ 2)) (ball 0 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hq : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := by fun_prop
  have hc : DifferentiableAt ℂ (fun w : ℂ => 1 - w ^ 2) z := by fun_prop
  have hp := (D5.S3.Analytic.OriginalHalfBinomialPeriod.picard_fuchs
    (norm_sq_lt_one hz1)).1.comp z hq
  have hl := hc.clog (one_sub_sq_mem_slitPlane hz1)
  exact (((hl.const_mul (1 / 4 : ℂ)).cexp).mul hp).differentiableWithinAt

/- Compare with the real theorem using the positive REAL logarithm. No principal
   logarithm of the determinant or of the period is used in this passage. -/
private lemma periodProduct_real {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    gaussianDet (t : ℂ) = Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - (t : ℂ) ^ 2)) *
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period ((t : ℂ) ^ 2) := by
  have hr1 : t ^ 2 < 1 := pow_lt_one₀ ht.le ht1 (by norm_num : (2 : ℕ) ≠ 0)
  have hb : 0 < (1 : ℝ) - t ^ 2 := by linarith
  have hcast : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) ^ 2 := by push_cast; rfl
  have hs : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht.le
  have he : Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - ((t ^ 2 : ℝ) : ℂ))) =
      (Real.rpow (1 - t ^ 2) (1 / 4 : ℝ) : ℂ) := by
    rw [show 1 - ((t ^ 2 : ℝ) : ℂ) = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hb.le,
      show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 1
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hb, mul_comm]
  calc
    gaussianDet (t : ℂ) = ((Real.rpow (1 - t ^ 2) (1 / 4 : ℝ) * F (t ^ 2) : ℝ) : ℂ) := by
      simpa only [hs] using gaussianDet_real_period_identity (sq_nonneg t) hr1
    _ = _ := by
      rw [← hcast, period_ofReal, he, Complex.ofReal_mul]

private lemma periodProduct_real_accum :
    ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      gaussianDet z = Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - z ^ 2)) *
        D5.S3.Analytic.OriginalHalfBinomialPeriod.period (z ^ 2) := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hne (n : ℕ) : (1 / ((n : ℂ) + 1)) ≠ 0 := by
    apply div_ne_zero one_ne_zero
    exact_mod_cast Nat.succ_ne_zero n
  have hp : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun n => by simpa using hne n)⟩
  apply hp.frequently
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
  have hsmall : (1 / ((n : ℝ) + 1)) < 1 :=
    (div_lt_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith)
  have hcast : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 1 / ((n : ℂ) + 1) := by
    push_cast
    rfl
  simpa only [hcast] using periodProduct_real hpos hsmall

/-- Full open complex disk, original signs, actual determinant and EXISTING
    period, with the principal branch paid by Re(1-z^2)>0. -/
theorem gaussianDet_complex_period_identity {z : ℂ} (hz : ‖z‖ < 1) :
    gaussianDet z = Complex.exp ((1 / 4 : ℂ) * Complex.log (1 - z ^ 2)) *
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period (z ^ 2) := by
  have hdOn : DifferentiableOn ℂ gaussianDet (ball (0 : ℂ) 1) :=
    gaussianDet_differentiableOn.mono (fun _ hw => mem_ball_zero_iff.mp hw)
  have hd := hdOn.analyticOnNhd isOpen_ball
  have hp := periodProduct_differentiableOn.analyticOnNhd isOpen_ball
  exact hd.eqOn_of_preconnected_of_frequently_eq hp isPreconnected_ball
    (by simp) periodProduct_real_accum (mem_ball_zero_iff.mpr hz)

/-- Nonvanishing of the existing period on its ENTIRE disk is a consequence of
    the proved determinant identity and its original exponential definition. -/
theorem period_ne_zero {x : ℂ} (hx : ‖x‖ < 1) :
    D5.S3.Analytic.OriginalHalfBinomialPeriod.period x ≠ 0 := by
  let z : ℂ := x ^ (2⁻¹ : ℂ)
  have hs : z ^ 2 = x := Complex.cpow_nat_inv_pow x (by norm_num : (2 : ℕ) ≠ 0)
  have hn : ‖z‖ ^ 2 = ‖x‖ := by rw [← norm_pow, hs]
  have hz : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  have he := gaussianDet_complex_period_identity hz
  rw [hs] at he
  intro hzero
  have hdet : gaussianDet z = 0 := by rw [he, hzero, mul_zero]
  exact Complex.exp_ne_zero (gaussianLogDet z) hdet

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
