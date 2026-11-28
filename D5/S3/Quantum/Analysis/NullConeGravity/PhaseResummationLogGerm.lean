/- GID: D5/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/PhaseResummationLogGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact logarithmic Clausen germ and two derivatives of the resummed phase. -/
import D5.S3.Quantum.Analysis.NullConeGravity.NonperturbativePhaseResummation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import D5.S3.Calculus.ClausenLocalGerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace D5.S3.Quantum.Analysis.NullConeGravity.PhaseResummationLogGerm

open NonperturbativePhaseResummation (modeTerm)
open Omega.Calculus.ClausenLocalGerms

private def z (r g : ℝ) : ℂ := (r : ℂ) * Complex.exp ((↑(-2 * g) : ℂ) * Complex.I)

private def term (r g : ℝ) (k : ℕ) : ℂ :=
  z r g ^ (k + 1) / ((k + 1 : ℕ) : ℂ) ^ 2

private def D (r g : ℝ) : ℂ := ∑' k : ℕ, term r g k

/-- The resummed phase built from the radial modes. -/
abbrev F (g : ℝ) : ℂ := ∑' k : ℕ, modeTerm g k

/-- The absolutely convergent sine series of order two. -/
def clausen2 (θ : ℝ) : ℝ :=
  ∑' k : ℕ, Real.sin (((k + 1 : ℕ) : ℝ) * θ) / ((k + 1 : ℕ) : ℝ) ^ 2

private lemma norm_z (r g : ℝ) : ‖z r g‖ = |r| := by
  rw [z, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

private lemma norm_term (r g : ℝ) (k : ℕ) :
    ‖term r g k‖ = |r| ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  rw [term, norm_div, norm_pow, norm_pow, norm_z, Complex.norm_natCast]

private lemma summable_inv_sq :
    Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) := by simp
  exact h.comp_injective Nat.succ_injective

private lemma summable_term {r : ℝ} (hr : |r| ≤ 1) (g : ℝ) : Summable (term r g) :=
  summable_inv_sq.of_norm_bounded fun k => by
    rw [norm_term]
    exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hr) (by positivity)

private lemma z_one_pow (g : ℝ) (k : ℕ) :
    z 1 g ^ (k + 1) = Complex.exp ((↑(-2 * ((k + 1 : ℕ) : ℝ) * g) : ℂ) * Complex.I) := by
  simp only [z, Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma F_eq_D (g : ℝ) : F g = ((g ^ 2 / 2 : ℝ) : ℂ) * D 1 g := by
  rw [F, D, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [modeTerm, term, z_one_pow]
  push_cast
  ring

private lemma D_im (g : ℝ) : (D 1 g).im = -clausen2 (2 * g) := by
  rw [clausen2, ← tsum_neg]
  refine (Complex.hasSum_im (summable_term (r := 1) (by norm_num) g).hasSum).tsum_eq.symm.trans ?_
  apply tsum_congr
  intro k
  rw [term, z_one_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.div_ofReal_im,
    Complex.exp_ofReal_mul_I_im]
  rw [show -2 * ((k + 1 : ℕ) : ℝ) * g = -(((k + 1 : ℕ) : ℝ) * (2 * g)) by ring,
    Real.sin_neg, neg_div]

/-- The imaginary part is the negative Clausen series with its original mode prefactor. -/
theorem phase_im_eq_neg_clausen (g : ℝ) : (F g).im = -(g ^ 2 / 2) * clausen2 (2 * g) := by
  rw [F_eq_D, Complex.im_ofReal_mul, D_im, mul_neg, neg_mul]

private lemma phase_im_neg (g : ℝ) : (F (-g)).im = -(F g).im := by
  have hθ (θ : ℝ) : clausen2 (-θ) = -clausen2 θ := by
    rw [clausen2, clausen2, ← tsum_neg]
    simp_rw [mul_neg, Real.sin_neg, neg_div]
  rw [phase_im_eq_neg_clausen, phase_im_eq_neg_clausen, neg_sq, mul_neg, hθ, mul_neg]

private lemma D_re (g : ℝ) :
    (D 1 g).re = ∑' k : ℕ, Real.cos (2 * ((k + 1 : ℕ) : ℝ) * g) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  refine (Complex.hasSum_re (summable_term (r := 1) (by norm_num) g).hasSum).tsum_eq.symm.trans ?_
  apply tsum_congr
  intro k
  rw [term, z_one_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.div_ofReal_re,
    Complex.exp_ofReal_mul_I_re]
  rw [show -2 * ((k + 1 : ℕ) : ℝ) * g = -(2 * ((k + 1 : ℕ) : ℝ) * g) by ring, Real.cos_neg]

set_option maxHeartbeats 600000 in
/-- The real part is the second Bernoulli polynomial times the mode prefactor. -/
theorem phase_re_eq_bernoulli (g : ℝ) (hg : |g| ≤ Real.pi) :
    (F g).re = Real.pi ^ 2 * g ^ 2 / 12 - Real.pi * |g| ^ 3 / 2 + g ^ 4 / 2 := by
  have hx : |g| / Real.pi ∈ Icc 0 1 :=
    ⟨div_nonneg (abs_nonneg _) Real.pi_pos.le, (div_le_one Real.pi_pos).mpr hg⟩
  have hc := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  change HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * (|g| / Real.pi)))
    ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / ((2 : ℕ).factorial : ℝ) *
      bernoulliFun 2 (|g| / Real.pi)) at hc
  rw [bernoulliFun_two] at hc
  let c := ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / ((2 : ℕ).factorial : ℝ) *
    ((|g| / Real.pi) ^ 2 - |g| / Real.pi + 6⁻¹))
  let f (n : ℕ) := 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * (|g| / Real.pi))
  have h0 : f 0 = 0 := by simp [f]
  have hh : HasSum f (c + ∑ k ∈ Finset.range 1, f k) := by simpa only [Finset.sum_range_one, h0, add_zero] using hc
  have hs := (hasSum_nat_add_iff 1 (f := f)).2 hh
  have hcos (n : ℕ) : Real.cos (2 * Real.pi * n * (|g| / Real.pi)) =
      Real.cos (2 * n * g) := by
    rw [show 2 * Real.pi * (n : ℝ) * (|g| / Real.pi) = 2 * n * |g| by
      field_simp [Real.pi_ne_zero]]
    rcases le_or_gt 0 g with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, Real.cos_neg]
  rw [F_eq_D, Complex.re_ofReal_mul, D_re]
  have heq : (∑' k : ℕ, Real.cos (2 * ((k + 1 : ℕ) : ℝ) * g) / ((k + 1 : ℕ) : ℝ) ^ 2) =
      ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / ((2 : ℕ).factorial : ℝ) *
        ((|g| / Real.pi) ^ 2 - |g| / Real.pi + 6⁻¹)) := by
    simpa only [f, c, hcos, one_div_mul_eq_div] using hs.tsum_eq
  rw [heq]
  norm_num
  have h4 : g ^ 4 = |g| ^ 4 := calc
    g ^ 4 = (g ^ 2) ^ 2 := by ring
    _ = (|g| ^ 2) ^ 2 := by rw [sq_abs]
    _ = |g| ^ 4 := by ring
  rw [← sq_abs g, h4]
  field_simp [Real.pi_ne_zero]
  ring

private lemma hasDerivAt_z (r g : ℝ) : HasDerivAt (z r) ((-2 * Complex.I) * z r g) g := by
  have h : HasDerivAt (fun x : ℝ => ((↑(-2 * x) : ℂ) * Complex.I)) (-2 * Complex.I) g := by
    convert ((Complex.ofRealCLM.hasDerivAt (x := g)).const_mul (-2 : ℂ)).mul_const Complex.I using 1
    · ext x
      push_cast
      rfl
    · change -2 * Complex.I = (-2 * 1) * Complex.I
      ring
  refine (h.cexp.const_mul (r : ℂ)).congr_deriv ?_
  unfold z
  ring

private lemma hasDerivAt_term (r g : ℝ) (k : ℕ) :
    HasDerivAt (fun x => term r x k)
      ((-2 * Complex.I) * (z r g ^ (k + 1) / ((k + 1 : ℕ) : ℂ))) g := by
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  unfold term
  refine (((hasDerivAt_z r g).pow (k + 1)).div_const (((k + 1 : ℕ) : ℂ) ^ 2)).congr_deriv ?_
  rw [Nat.add_sub_cancel]
  field_simp [hk]
  rw [pow_succ]

private lemma hasDerivAt_D {r : ℝ} (hr : |r| < 1) (g : ℝ) :
    HasDerivAt (D r) (2 * Complex.I * Complex.log (1 - z r g)) g := by
  have hs : Summable (fun k : ℕ => 2 * |r| ^ (k + 1)) :=
    ((summable_geometric_of_lt_one (abs_nonneg _) hr).comp_injective Nat.succ_injective).mul_left 2
  have hb (k : ℕ) (x : ℝ) :
      ‖(-2 * Complex.I) * (z r x ^ (k + 1) / ((k + 1 : ℕ) : ℂ))‖ ≤
        2 * |r| ^ (k + 1) := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_I, mul_one, norm_div,
      norm_pow, norm_z, Complex.norm_natCast]
    gcongr
    exact div_le_self (pow_nonneg (abs_nonneg _) _) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have h := hasDerivAt_tsum hs (fun k x => hasDerivAt_term r x k) hb (summable_term hr.le 0) g
  have hlog := (Complex.hasSum_taylorSeries_neg_log' (z := z r g)
    (by simpa [norm_z] using hr)).mul_left (-2 * Complex.I)
  have heq : (∑' k : ℕ, (-2 * Complex.I) * (z r g ^ (k + 1) / ((k + 1 : ℕ) : ℂ))) =
      -2 * Complex.I * -Complex.log (1 - z r g) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog.tsum_eq
  rw [heq] at h
  refine h.congr_deriv ?_
  ring

private def L (r g : ℝ) : ℝ := Real.log ‖1 - z r g‖

private lemma continuous_L {r : ℝ} (hr : |r| < 1) : Continuous (L r) := by
  apply Continuous.log (by unfold z; fun_prop)
  intro g
  have hn : ‖z r g‖ < 1 := by simpa [norm_z] using hr
  have hz : z r g ≠ 1 := by
    intro h
    simp [h] at hn
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm)

private lemma abel_integral {r : ℝ} (hr : |r| < 1) (g : ℝ) :
    (D r g).im = 2 * ∫ t in 0..g, L r t := by
  have hz : (D r 0).im = 0 := by
    have h₀ := Complex.hasSum_im (summable_term hr.le 0).hasSum
    have ht (k : ℕ) : (term r 0 k).im = 0 := by
      simp only [term, z, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_div]
      exact Complex.ofReal_im _
    change HasSum (fun k => (term r 0 k).im) (D r 0).im at h₀
    simp only [ht] at h₀
    simpa only [tsum_zero] using h₀.tsum_eq.symm
  have hd (t : ℝ) : HasDerivAt (fun x => (D r x).im) (2 * L r t) t := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_D hr t)
    change HasDerivAt (fun x => (D r x).im) (2 * L r t) t
    refine h.congr_deriv ?_
    change (2 * Complex.I * Complex.log (1 - z r t)).im = _
    simp [L, Complex.mul_im, Complex.log_re]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (((continuous_L hr).const_mul 2).intervalIntegrable 0 g)
  rwa [intervalIntegral.integral_const_mul, hz, sub_zero, eq_comm] at hi

private lemma norm_sub_z_sq (r g : ℝ) :
    ‖1 - z r g‖ ^ 2 = (1 - r) ^ 2 + 4 * r * Real.sin g ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_sub]
  have hz : Complex.normSq (z r g) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_z, sq_abs]
  change Complex.normSq 1 + Complex.normSq (z r g) -
    2 * (1 * (starRingEnd ℂ) (z r g)).re = _
  rw [hz, Complex.normSq_one, one_mul, Complex.conj_re, z, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, show -2 * g = -(2 * g) by ring, Real.cos_neg,
    Real.cos_two_mul, Real.cos_sq']
  ring

private lemma norm_sub_z_one {g : ℝ} (hg : 0 ≤ Real.sin g) :
    ‖1 - z 1 g‖ = 2 * Real.sin g := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sub_z_sq]
  ring

private def radius (j : ℕ) : ℝ := 1 - 1 / (j + 2 : ℝ)

private lemma radius_bounds (j : ℕ) : 1 / 2 ≤ radius j ∧ radius j < 1 := by
  have h₁ : (1 : ℝ) / (j + 2 : ℝ) ≤ 1 / 2 := by
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg j)
  have h₂ : (0 : ℝ) < 1 / (j + 2 : ℝ) := by positivity
  unfold radius
  constructor <;> linarith

private lemma tendsto_radius : Tendsto radius atTop (𝓝 1) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  convert hh using 1
  · ext j
    simp [radius, Nat.cast_add]
    ring
  · simp

private lemma tendsto_D (g : ℝ) : Tendsto (fun j => D (radius j) g) atTop (𝓝 (D 1 g)) := by
  apply tendsto_tsum_of_dominated_convergence summable_inv_sq
  · intro k
    exact ((show Continuous (fun r => term r g k) by unfold term z; fun_prop).tendsto 1).comp
      tendsto_radius
  · exact Eventually.of_forall fun j k => by
      have h := radius_bounds j
      rw [norm_term, abs_of_nonneg (by linarith : 0 ≤ radius j)]
      exact div_le_div_of_nonneg_right (pow_le_one₀ (by linarith) h.2.le) (by positivity)

private lemma abel_log_bound {r t : ℝ} (hr₁ : 1 / 2 ≤ r) (hr₂ : r ≤ 1)
    (ht₁ : 0 < t) (ht₂ : t < Real.pi) :
    ‖L r t‖ ≤ Real.log 2 + |Real.log (Real.sin t)| := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht₁ ht₂
  have hlo : Real.sin t ≤ ‖1 - z r t‖ := by
    apply (sq_le_sq₀ hs.le (norm_nonneg _)).mp
    rw [norm_sub_z_sq]
    have h : 0 ≤ (4 * r - 1) * Real.sin t ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [sq_nonneg (1 - r)]
  have hhi : ‖1 - z r t‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖z r t‖ := norm_sub_le ..
      _ ≤ 2 := by rw [norm_z, norm_one, abs_of_nonneg (by linarith)]; linarith
  rw [Real.norm_eq_abs, abs_le]
  have hloglo := Real.log_le_log hs hlo
  have hloghi := Real.log_le_log (hs.trans_le hlo) hhi
  have ha := neg_abs_le (Real.log (Real.sin t))
  have hb := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  unfold L
  constructor <;> linarith [abs_nonneg (Real.log (Real.sin t))]

private lemma tendsto_log_integral {g : ℝ} (hg : g ∈ Icc 0 Real.pi) :
    Tendsto (fun j => ∫ t in 0..g, L (radius j) t) atTop
      (𝓝 (∫ t in 0..g, Real.log (2 * Real.sin t))) := by
  have hr j : |radius j| < 1 := by
    have h := radius_bounds j
    rw [abs_of_nonneg (by linarith : 0 ≤ radius j)]
    exact h.2
  have hpi : ∀ᵐ t ∂volume, t ≠ Real.pi := volume.ae_ne Real.pi
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t => Real.log 2 + |Real.log (Real.sin t)|)
  · exact Eventually.of_forall fun j => (continuous_L (hr j)).aestronglyMeasurable
  · refine Eventually.of_forall fun j => hpi.mono fun t ht hmem => ?_
    rw [uIoc_of_le hg.1] at hmem
    exact abel_log_bound (radius_bounds j).1 (radius_bounds j).2.le hmem.1
      (lt_of_le_of_ne (hmem.2.trans hg.2) ht)
  · exact (intervalIntegrable_const).add (intervalIntegrable_log_sin.abs)
  · refine hpi.mono fun t ht hmem => ?_
    rw [uIoc_of_le hg.1] at hmem
    have hsin := Real.sin_pos_of_pos_of_lt_pi hmem.1 (lt_of_le_of_ne (hmem.2.trans hg.2) ht)
    have hnorm := norm_sub_z_one hsin.le
    have hp : ‖1 - z 1 t‖ ≠ 0 := by rw [hnorm]; positivity
    have hc : ContinuousAt (fun r : ℝ => Real.log ‖1 - z r t‖) 1 :=
      ContinuousAt.log (by unfold z; fun_prop) hp
    simpa only [L, hnorm, Function.comp_def] using hc.tendsto.comp tendsto_radius

/-- The phase on the positive interval is the primitive of the logarithmic sine kernel. -/
theorem phase_im_eq_integral (g : ℝ) (hg : g ∈ Icc 0 Real.pi) :
    (F g).im = g ^ 2 * ∫ t in 0..g, Real.log (2 * Real.sin t) := by
  have h₁ : Tendsto (fun j => (D (radius j) g).im) atTop (𝓝 ((D 1 g).im)) :=
    Complex.continuous_im.continuousAt.tendsto.comp (tendsto_D g)
  have h₂ := tendsto_const_nhds (x := (2 : ℝ)) |>.mul (tendsto_log_integral hg)
  have heq (j : ℕ) : (D (radius j) g).im = 2 * ∫ t in 0..g, L (radius j) t := by
    apply abel_integral
    have h := radius_bounds j
    rw [abs_of_nonneg (by linarith : 0 ≤ radius j)]
    exact h.2
  simp_rw [← heq] at h₂
  rw [F_eq_D, Complex.im_ofReal_mul, tendsto_nhds_unique h₁ h₂]
  ring

private def U : Set ℝ := Ioo (-Real.pi) Real.pi

private lemma mem_U {g : ℝ} : g ∈ U ↔ |g| < Real.pi := abs_lt.symm

private lemma zero_mem_U : (0 : ℝ) ∈ U := mem_U.2 (by simp [Real.pi_pos])

private lemma U_eventually {g : ℝ} (hg : g ∈ U) : ∀ᶠ x in 𝓝 g, x ∈ U :=
  isOpen_Ioo.eventually_mem hg

/-- The cubic logarithmic term expressed using the absolute coupling. -/
def cubicGerm (g : ℝ) : ℝ := g ^ 3 * (Real.log (2 * |g|) - 1)

private lemma im_eq_cubic_add {g : ℝ} (hg : g ∈ U) :
    (F g).im = cubicGerm g + g ^ 2 * primitive g := by
  have hpos (x : ℝ) (h₀ : 0 ≤ x) (hπ : x < Real.pi) :
      (F x).im = cubicGerm x + x ^ 2 * primitive x := by
    rw [phase_im_eq_integral x ⟨h₀, hπ.le⟩]
    have hx : x ∈ U := mem_U.2 (by rwa [abs_of_nonneg h₀])
    have hi : (∫ t in 0..x, Real.log (2 * Real.sin t)) =
        ∫ t in 0..x, (Real.log 2 + Real.log t) + sincLog t := by
      apply intervalIntegral.integral_congr_ae
      rw [uIoc_of_le h₀]
      exact Eventually.of_forall fun t ht => by
        have hsin := Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans_lt hπ)
        have hsinc := Real.sinc_pos (by rw [abs_of_pos ht.1]; exact ht.2.trans_lt hπ : |t| < Real.pi)
        rw [Real.log_mul two_ne_zero hsin.ne', sincLog, Real.sinc_of_ne_zero ht.1.ne',
          Real.log_div hsin.ne' ht.1.ne']
        ring
    rw [hi, intervalIntegral.integral_add (intervalIntegrable_const.add intervalIntegral.intervalIntegrable_log')
      (intervalIntegrable_sincLog hx), intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_log', intervalIntegral.integral_const,
      integral_log_from_zero, cubicGerm, abs_of_nonneg h₀]
    by_cases h : x = 0
    · simp [h]
    · rw [Real.log_mul two_ne_zero h]
      simp only [sub_zero, smul_eq_mul, primitive]
      ring
  rcases le_or_gt 0 g with h | h
  · exact hpos g h (abs_lt.mp (mem_U.1 hg)).2
  · have hh := hpos (-g) (by linarith) (by linarith [(abs_lt.mp (mem_U.1 hg)).1])
    rw [phase_im_neg, primitive_neg, neg_sq] at hh
    have hneg : cubicGerm (-g) = -cubicGerm g := by
      unfold cubicGerm
      rw [abs_neg]
      ring
    rw [hneg] at hh
    linarith

private lemma J_bound {g : ℝ} (hg₀ : 0 ≤ g) (hg₁ : g ≤ 1) : |primitive g| ≤ g ^ 3 / 15 := by
  have hg : g ∈ U := mem_U.2 (by rw [abs_of_nonneg hg₀]; linarith [Real.pi_gt_three])
  calc
    |primitive g| ≤ ∫ t in 0..g, |sincLog t| := intervalIntegral.abs_integral_le_integral_abs hg₀
    _ ≤ ∫ t in 0..g, t ^ 2 / 5 :=
      intervalIntegral.integral_mono_on hg₀ (intervalIntegrable_sincLog hg).abs
        ((show Continuous (fun t : ℝ => t ^ 2 / 5) by fun_prop).intervalIntegrable 0 g)
        (fun t ht => sincLog_bound ht.1 (ht.2.trans hg₁))
    _ = g ^ 3 / 15 := by rw [intervalIntegral.integral_div, integral_pow]; norm_num; ring

/-- The remainder after the exact logarithmic cubic is bounded by the fifth power. -/
theorem phase_im_cubic_bound (g : ℝ) (hg : |g| ≤ 1) :
    |(F g).im - cubicGerm g| ≤ |g| ^ 5 / 15 := by
  rw [im_eq_cubic_add (mem_U.2 (by linarith [Real.pi_gt_three] : |g| < Real.pi)),
    add_sub_cancel_left, abs_mul, abs_pow]
  have h : |primitive g| ≤ |g| ^ 3 / 15 := by
    rcases le_or_gt 0 g with h₀ | h₀
    · simp only [abs_of_nonneg h₀] at hg ⊢
      exact J_bound h₀ hg
    · rw [abs_of_neg h₀] at hg ⊢
      simpa [primitive_neg] using J_bound (neg_nonneg.mpr h₀.le) hg
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by ring)

/-- The right-neighborhood Clausen expansion with its exact logarithmic coefficient. -/
theorem phase_im_right_germ :
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
      (fun g : ℝ => (F g).im + g ^ 3 * Real.log (1 / g) -
        (Real.log 2 - 1) * g ^ 3) (fun g : ℝ => g ^ 5) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / 15, ?_⟩
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with g h₀ h₁
  change 0 < g at h₀
  change g < 1 at h₁
  have h := phase_im_cubic_bound g (by rw [abs_of_pos h₀]; exact h₁.le)
  rw [cubicGerm, abs_of_pos h₀, Real.log_mul two_ne_zero h₀.ne'] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, Real.log_div one_ne_zero h₀.ne', Real.log_one]
  rw [show (F g).im + g ^ 3 * (0 - Real.log g) - (Real.log 2 - 1) * g ^ 3 =
    (F g).im - g ^ 3 * (Real.log 2 + Real.log g - 1) by ring]
  rw [abs_of_pos h₀]
  linarith

private def imRemainder (g : ℝ) : ℝ := (Real.log 2 - 1) * g ^ 3 + g ^ 2 * primitive g

private lemma im_eq_model {g : ℝ} (hg : g ∈ U) :
    (F g).im = logCubic g + imRemainder g := by
  rw [im_eq_cubic_add hg]
  by_cases h : g = 0
  · simp [h, cubicGerm, logCubic, imRemainder]
  · rw [cubicGerm, Real.log_mul two_ne_zero (abs_ne_zero.mpr h), Real.log_abs]
    unfold logCubic imRemainder
    ring

private lemma contDiffOn_remainder : ContDiffOn ℝ ∞ imRemainder U := by
  unfold imRemainder
  exact (by fun_prop : ContDiffOn ℝ ∞ (fun g : ℝ => (Real.log 2 - 1) * g ^ 3) U).add
    ((contDiff_id.pow 2).contDiffOn.mul contDiffOn_primitive)

private def realModel (g : ℝ) : ℝ :=
  Real.pi ^ 2 * g ^ 2 / 12 - Real.pi * |g| ^ 3 / 2 + g ^ 4 / 2

private lemma contDiff_realModel : ContDiff ℝ 2 realModel := by
  unfold realModel
  have h₁ : ContDiff ℝ 2 (fun g : ℝ => Real.pi ^ 2 * g ^ 2 / 12) := by fun_prop
  have h₂ : ContDiff ℝ 2 (fun g : ℝ => Real.pi * |g| ^ 3 / 2) :=
    (contDiff_const.mul contDiff_absCube).div_const 2
  exact (h₁.sub h₂).add (by fun_prop)

private lemma realModel_deriv_two : iteratedDeriv 2 realModel 0 = Real.pi ^ 2 / 6 := by
  have hd (x : ℝ) : HasDerivAt realModel
      (Real.pi ^ 2 * x / 6 - (Real.pi * 3) * (x * |x|) / 2 + 2 * x ^ 3) x := by
    have h := (((((hasDerivAt_id x).pow 2).const_mul (Real.pi ^ 2)).div_const 12).sub
      (((absCube_hasDerivAt x).const_mul Real.pi).div_const 2)).add
        (((hasDerivAt_id x).pow 4).div_const 2)
    exact h.congr_deriv (by dsimp [id]; ring)
  rw [iteratedDeriv_succ, iteratedDeriv_one, funext fun x => (hd x).deriv]
  have h := (((((hasDerivAt_id (0 : ℝ)).const_mul (Real.pi ^ 2)).div_const 6).sub
    (((mulAbs_hasDerivAt 0).const_mul (Real.pi * 3)).div_const 2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul 2))
  simpa [id, Pi.add_def, Pi.sub_def, Pi.pow_def] using h.deriv

private lemma im_contDiffOn :
    ContDiffOn ℝ 2 (fun g => (F g).im) U :=
  (contDiff_logCubic.contDiffOn.add (contDiffOn_remainder.of_le (by norm_num))).congr
    (fun _ hg => im_eq_model hg)

private lemma re_contDiffOn :
    ContDiffOn ℝ 2 (fun g => (F g).re) U :=
  contDiff_realModel.contDiffOn.congr fun g hg => phase_re_eq_bernoulli g (mem_U.1 hg).le

/-- The resummed phase is twice continuously differentiable across zero. -/
theorem phase_contDiffOn_two : ContDiffOn ℝ 2 F (Ioo (-Real.pi) Real.pi) := by
  have hr := Complex.ofRealCLM.contDiff.contDiffOn.comp re_contDiffOn (mapsTo_univ _ _)
  have hi := Complex.ofRealCLM.contDiff.contDiffOn.comp im_contDiffOn (mapsTo_univ _ _)
  have hc : ContDiffOn ℝ 2 (fun _ : ℝ => Complex.I) U := contDiffOn_const
  exact (hr.add (hi.mul hc)).congr fun g _ => (Complex.re_add_im (F g)).symm

/-- In particular the resummation is of class C² at zero. -/
theorem phase_contDiffAt_two : ContDiffAt ℝ 2 F 0 :=
  phase_contDiffOn_two.contDiffAt (isOpen_Ioo.mem_nhds zero_mem_U)

/-- The first derivative vanishes at zero by the quadratic bound for the whole series. -/
theorem phase_hasDerivAt_zero : HasDerivAt F 0 0 := by
  have hz : F 0 = 0 := by simp [F, modeTerm]
  rw [hasDerivAt_iff_tendsto_slope, tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun g : ℝ => |g|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using (continuous_abs.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      nhdsWithin_le_nhds
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) hlim
  rw [slope_def_module, hz, sub_zero, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs]
  by_cases hg : g = 0
  · simp [hg]
  calc
    _ ≤ |g|⁻¹ * g ^ 2 := mul_le_mul_of_nonneg_left
      (NonperturbativePhaseResummation.summable_and_norm_le_modeTerm g).2 (by positivity)
    _ = |g| := by rw [← sq_abs g, pow_two, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hg), one_mul]

private lemma phase_differentiable {g : ℝ} (hg : g ∈ U) : DifferentiableAt ℝ F g :=
  (phase_contDiffOn_two.contDiffAt (isOpen_Ioo.mem_nhds hg)).differentiableAt (by norm_num)

private lemma phase_derivative_differentiable {g : ℝ} (hg : g ∈ U) :
    DifferentiableAt ℝ (deriv F) g :=
  ((phase_contDiffOn_two.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).contDiffAt
    (isOpen_Ioo.mem_nhds hg)).differentiableAt (by norm_num)

private lemma component_deriv (L : ℂ →L[ℝ] ℝ) {g : ℝ} (hg : g ∈ U) :
    deriv (fun x => L (F x)) g = L (deriv F g) :=
  (L.hasFDerivAt.comp_hasDerivAt g (phase_differentiable hg).hasDerivAt).deriv

private lemma component_deriv_two (L : ℂ →L[ℝ] ℝ) {g : ℝ} (hg : g ∈ U) :
    iteratedDeriv 2 (fun x => L (F x)) g = L (iteratedDeriv 2 F g) := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have he : deriv (fun x => L (F x)) =ᶠ[𝓝 g] fun x => L (deriv F x) :=
    (U_eventually hg).mono fun x hx => component_deriv L hx
  rw [he.deriv_eq]
  exact (L.hasFDerivAt.comp_hasDerivAt g (phase_derivative_differentiable hg).hasDerivAt).deriv

private lemma im_deriv_two_model {g : ℝ} (hg : g ∈ U) :
    iteratedDeriv 2 (fun x => (F x).im) g = logCubicDD g + iteratedDeriv 2 imRemainder g := by
  have he : (fun x => (F x).im) =ᶠ[𝓝 g] (fun x => logCubic x + imRemainder x) :=
    (U_eventually hg).mono fun _ hx => im_eq_model hx
  rw [he.iteratedDeriv_eq, iteratedDeriv_fun_add contDiff_logCubic.contDiffAt
    ((contDiffOn_remainder.of_le (by norm_num)).contDiffAt (isOpen_Ioo.mem_nhds hg))]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [funext fun x => (logCubic_hasDerivAt x).deriv, (logCubicD_hasDerivAt g).deriv]

private lemma im_remainder_deriv_two_zero : iteratedDeriv 2 imRemainder 0 = 0 := by
  have hJ : ContDiffAt ℝ 2 primitive 0 :=
    (contDiffOn_primitive.of_le (by norm_num)).contDiffAt (isOpen_Ioo.mem_nhds zero_mem_U)
  unfold imRemainder
  have h1 : ContDiffAt ℝ 2 (fun g : ℝ => g ^ 2 * primitive g) 0 := (by fun_prop : ContDiffAt ℝ 2 (fun g : ℝ => g ^ 2) 0).mul hJ
  rw [iteratedDeriv_fun_add (by fun_prop) h1,
    iteratedDeriv_fun_mul (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_mul (by fun_prop) hJ]
  simp [Finset.sum_range_succ, primitive]

/-- The second derivative at zero is fixed by the real Bernoulli term. -/
theorem phase_iteratedDeriv_two_zero :
    iteratedDeriv 2 F 0 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re, ← show iteratedDeriv 2 (fun x => (F x).re) 0 =
      (iteratedDeriv 2 F 0).re from component_deriv_two Complex.reCLM zero_mem_U]
    have he : (fun x => (F x).re) =ᶠ[𝓝 (0 : ℝ)] realModel :=
      (U_eventually zero_mem_U).mono fun x hx => phase_re_eq_bernoulli x (mem_U.1 hx).le
    exact (he.iteratedDeriv_eq 2).trans realModel_deriv_two
  · rw [Complex.ofReal_im, ← show iteratedDeriv 2 (fun x => (F x).im) 0 =
      (iteratedDeriv 2 F 0).im from component_deriv_two Complex.imCLM zero_mem_U,
      im_deriv_two_model zero_mem_U, im_remainder_deriv_two_zero]
    simp [logCubicDD]

/-- The derivative of the resummed phase has the stated derivative at zero. -/
theorem phase_deriv_hasDerivAt_zero :
    HasDerivAt (deriv F) ((Real.pi ^ 2 / 6 : ℝ) : ℂ) 0 := by
  rw [← phase_iteratedDeriv_two_zero, iteratedDeriv_succ, iteratedDeriv_one]
  exact (phase_derivative_differentiable zero_mem_U).hasDerivAt

/-- The logarithmic quotient of the second derivative diverges on the right of zero. -/
theorem phase_im_second_not_differentiable :
    ¬ DifferentiableAt ℝ (iteratedDeriv 2 (fun g : ℝ => (F g).im)) 0 := by
  intro hd
  have hr : DifferentiableAt ℝ (iteratedDeriv 2 imRemainder) 0 := by
    have h := (contDiffOn_remainder.deriv_of_isOpen isOpen_Ioo (m := ∞) le_rfl)
      |>.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    exact (h.contDiffAt (isOpen_Ioo.mem_nhds zero_mem_U)).differentiableAt (by norm_num)
  apply logCubicDD_not_differentiable
  refine (hd.sub hr).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds zero_mem_U] with g hg
  rw [Pi.sub_apply, im_deriv_two_model hg, add_sub_cancel_right]

/-- The complex second derivative also has no derivative at zero. -/
theorem phase_second_no_hasDerivAt (d : ℂ) : ¬ HasDerivAt (deriv (deriv F)) d 0 := by
  intro hd
  apply phase_im_second_not_differentiable
  refine ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd).differentiableAt).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds zero_mem_U] with g hg
  simpa only [Function.comp_def, iteratedDeriv_succ, iteratedDeriv_zero, Complex.imCLM_apply] using
    component_deriv_two Complex.imCLM hg

end D5.S3.Quantum.Analysis.NullConeGravity.PhaseResummationLogGerm
