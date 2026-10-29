/- GID: D5/S3/Weil/Mertens/ActualThetaTailLaplace
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/ActualThetaTailLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual activation-weighted theta tails in logarithmic coordinates. -/

import D5.S3.Weil.Mertens.WeightedPrimeLimit
import D5.S3.Weil.Mertens.ThetaLaplaceContinuation
import D5.S3.Arith.Robin.ActualRobinClockCovariance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The signed theta tail uses the actual reciprocal logarithmic activation density. -/

namespace D5.S3.Weil.Mertens.ActualThetaTailLaplace

open Real Set MeasureTheory Filter
open scoped Topology
open ThetaLaplaceContinuation (q Q)

noncomputable section

/-- The logarithmic lower threshold. -/
def u₀ : ℝ := Real.log 2

/-- The actual activation-weighted source in logarithmic coordinates. -/
def k (u : ℝ) : ℝ := q u * (u + 1) / u ^ 2

/-- The original signed tail in the original real variable. -/
def F (x : ℝ) : ℝ :=
  -(∫ t in Ioi x, (Chebyshev.theta t - t) *
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t)

/-- The logarithmic signed tail. -/
def f (u : ℝ) : ℝ := -(∫ v in Ioi u, k v)

/-- The actual cutoff Laplace transform of the signed tail. -/
def L (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) * (f u : ℂ)

private lemma u₀_pos : 0 < u₀ := Real.log_pos (by norm_num)

private lemma theta_kernel_integrable :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) (Ioi 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hr : IntegrableOn (fun t : ℝ => Real.sqrt t / t ^ 2) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := (1 / 2 : ℝ) - 2)
      (by norm_num) one_pos).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    dsimp only
    rw [Real.sqrt_eq_rpow, Real.rpow_sub ht0, Real.rpow_two]
  have hm : Measurable (fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) :=
    (Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).div
      (measurable_id.pow_const 2)
  have hd : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      (Ioi 1) := by
    refine (hr.const_mul C).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)),
      abs_of_nonneg (sq_nonneg t)]
    exact (div_le_div_of_nonneg_right (hC t) (sq_nonneg t)).trans_eq (by ring)
  convert WeightedPrimeLimit.chebyshev_error_kernel_integrable.sub hd using 1
  ext t
  change (Chebyshev.theta t - t) / t ^ 2 =
    (Chebyshev.psi t - t) / t ^ 2 - (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2
  ring

private lemma q_integrable : IntegrableOn q (Ioi u₀) := by
  have ht := theta_kernel_integrable.mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2))
  have he := (integrableOn_comp_exp_Ioi
    (fun t : ℝ => (Chebyshev.theta t - t) / t ^ 2) u₀).mpr
    (by simpa only [u₀, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using ht)
  refine he.congr_fun ?_ measurableSet_Ioi
  intro u _
  dsimp [q]
  rw [Real.exp_neg]
  field_simp

private lemma q_measurable : Measurable q := by
  unfold q
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-u))).mul
    ((Chebyshev.theta_mono.measurable.comp (by fun_prop)).sub (by fun_prop))

private lemma k_measurable : Measurable k :=
  ((q_measurable.mul (measurable_id.add_const 1)).div (measurable_id.pow_const 2))

private lemma weight_bound {u : ℝ} (hu : u₀ ≤ u) :
    0 ≤ (u + 1) / u ^ 2 ∧ (u + 1) / u ^ 2 ≤ (u₀ + 1) / u₀ ^ 2 := by
  have h0 := u₀_pos
  have hu0 : 0 < u := h0.trans_le hu
  constructor
  · positivity
  · have hi : 1 / u ≤ 1 / u₀ := one_div_le_one_div_of_le h0 hu
    have hi2 : 1 / u ^ 2 ≤ 1 / u₀ ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos h0) (pow_le_pow_left₀ h0.le hu 2)
    calc
      (u + 1) / u ^ 2 = 1 / u + 1 / u ^ 2 := by field_simp
      _ ≤ 1 / u₀ + 1 / u₀ ^ 2 := add_le_add hi hi2
      _ = (u₀ + 1) / u₀ ^ 2 := by field_simp

private lemma k_integrable : IntegrableOn k (Ioi u₀) := by
  refine (q_integrable.norm.const_mul ((u₀ + 1) / u₀ ^ 2)).mono'
    k_measurable.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [k, show q u * (u + 1) / u ^ 2 = q u * ((u + 1) / u ^ 2) by ring, norm_mul]
  have hw := weight_bound hu.le
  have hn : ‖(u + 1) / u ^ 2‖ ≤ (u₀ + 1) / u₀ ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2
  exact (mul_le_mul_of_nonneg_left hn (norm_nonneg (q u))).trans_eq (mul_comm _ _)

private lemma exp_activation (u : ℝ) :
    Real.exp u * ((Chebyshev.theta (Real.exp u) - Real.exp u) *
      D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity (Real.exp u)) = k u := by
  dsimp [D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity, k, q]
  rw [Real.log_exp, Real.exp_neg]
  field_simp

private lemma original_integrable {U : ℝ} (hU : u₀ ≤ U) :
    IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
      D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) (Ioi (Real.exp U)) := by
  apply (integrableOn_comp_exp_Ioi _ U).mp
  refine (k_integrable.mono_set (Ioi_subset_Ioi hU)).congr_fun ?_ measurableSet_Ioi
  intro u _
  exact (exp_activation u).symm

private lemma tail_substitution (u : ℝ) : f u = F (Real.exp u) := by
  unfold f F
  congr 1
  have h := integral_comp_exp_Ioi (fun t : ℝ => (Chebyshev.theta t - t) *
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) u
  simpa only [smul_eq_mul, exp_activation] using h

private lemma tail_increment {a b : ℝ} (ha : u₀ ≤ a) (hb : u₀ ≤ b) :
    f b = f a + ∫ v in a..b, k v := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    (k_integrable.mono_set (Ioi_subset_Ioi ha))
    (k_integrable.mono_set (Ioi_subset_Ioi hb))
  dsimp [f]
  linarith

private lemma tail_bound {u : ℝ} (hu : u₀ ≤ u) :
    ‖f u‖ ≤ ∫ v in Ioi u₀, ‖k v‖ := by
  rw [f, norm_neg]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_set k_integrable.norm (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun _ h => lt_of_le_of_lt hu h))

private lemma tail_tendsto : Tendsto f atTop (𝓝 0) := by
  change Tendsto (fun u => -(∫ v in Ioi u, k v)) atTop (𝓝 0)
  simpa only [id_eq, neg_zero] using
    (tendsto_integral_Ioi_zero (f := k) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)).neg

private lemma tail_ac {a b : ℝ} (ha : u₀ ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval f a b := by
  have hi : IntervalIntegrable k volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact k_integrable.mono_set (fun v hv => lt_of_le_of_lt ha hv.1)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  apply (hc.add (hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp))).congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact (tail_increment ha (ha.trans hu.1)).symm

private lemma weighted_k_integrable :
    IntegrableOn (fun v : ℝ => (v - u₀) * ‖k v‖) (Ioi u₀) := by
  refine (q_integrable.norm.mul_const (1 + 1 / u₀)).mono'
    ((measurable_id.sub_const u₀).mul k_measurable.norm).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := u₀_pos.trans hv
  have hw := weight_bound hv.le
  have hk : ‖k v‖ = ‖q v‖ * ((v + 1) / v ^ 2) := by
    rw [k, show q v * (v + 1) / v ^ 2 = q v * ((v + 1) / v ^ 2) by ring,
      norm_mul, Real.norm_eq_abs ((v + 1) / v ^ 2), abs_of_nonneg hw.1]
  have hcoef : (v - u₀) * ((v + 1) / v ^ 2) ≤ 1 + 1 / u₀ := by
    calc
      _ ≤ v * ((v + 1) / v ^ 2) := mul_le_mul_of_nonneg_right (sub_le_self _ u₀_pos.le) hw.1
      _ = 1 + 1 / v := by field_simp
      _ ≤ 1 + 1 / u₀ := add_le_add le_rfl (one_div_le_one_div_of_le u₀_pos hv.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hv.le) (norm_nonneg _)), hk]
  nlinarith [mul_le_mul_of_nonneg_left hcoef (norm_nonneg (q v))]

private lemma tail_integrable : IntegrableOn f (Ioi u₀) := by
  let G : ℝ × ℝ → ℝ := fun p => if u₀ < p.2 ∧ p.2 ≤ p.1 then k p.1 else 0
  have hGm : Measurable G :=
    (k_measurable.comp measurable_fst).ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)) measurable_const
  have hGe (v : ℝ) : (fun u => G (v, u)) = (Ioc u₀ v).indicator (fun _ => k v) := by
    funext u
    simp [G, Set.indicator_apply]
  have hGi (v : ℝ) : Integrable (fun u => G (v, u)) := by
    rw [hGe]
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have hGn (v : ℝ) (hv : u₀ < v) :
      (∫ u : ℝ, ‖G (v, u)‖) = (v - u₀) * ‖k v‖ := by
    simp_rw [show ∀ u, G (v, u) = (Ioc u₀ v).indicator (fun _ => k v) u from
      fun u => congrFun (hGe v) u]
    simp only [norm_indicator_eq_indicator_norm, integral_indicator measurableSet_Ioc,
      integral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hv.le),
      smul_eq_mul, Measure.restrict_apply_univ]
  have hG : Integrable G ((volume.restrict (Ioi u₀)).prod volume) := by
    apply (integrable_prod_iff hGm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hGi, ?_⟩
    exact weighted_k_integrable.congr_fun (fun v hv => (hGn v hv).symm) measurableSet_Ioi
  have hinner {u : ℝ} (hu : u₀ < u) :
      (∫ v in Ioi u₀, G (v, u)) = ∫ v in Ioi u, k v := by
    have he : (fun v => G (v, u)) = (Ici u).indicator k := by
      funext v
      simp [G, hu, Set.indicator_apply]
    rw [he, setIntegral_indicator measurableSet_Ici,
      show Ioi u₀ ∩ Ici u = Ici u from
        inter_eq_right.mpr (fun v hv => lt_of_lt_of_le hu hv), integral_Ici_eq_integral_Ioi]
  refine (hG.integral_prod_right.neg.integrableOn).congr_fun ?_ measurableSet_Ioi
  intro u hu
  change -(∫ v in Ioi u₀, G (v, u)) = f u
  rw [hinner hu]
  rfl

private lemma tail_ae_deriv :
    ∀ᵐ u ∂volume.restrict (Ioi u₀), HasDerivAt f (k u) u := by
  let k₀ := (Ioi u₀).indicator k
  have hi : Integrable k₀ := (integrable_indicator_iff measurableSet_Ioi).mpr k_integrable
  have hp := LocallyIntegrable.ae_hasDerivAt_integral hi.locallyIntegrable
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem measurableSet_Ioi] with u hu huu
  have he : ∀ v ∈ Ioi u₀, f u₀ + ∫ t in u₀..v, k₀ t = f v := by
    intro v hv
    rw [tail_increment le_rfl hv.le]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hv.le] at ht
    exact Set.indicator_of_mem ht.1 k
  have hd := (hasDerivAt_const u (f u₀)).add (hu u₀)
  rw [zero_add, show k₀ u = k u from Set.indicator_of_mem huu k] at hd
  exact hd.congr_of_eventuallyEq
    (Filter.EventuallyEq.symm (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds huu) he))

private def P (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)) * (f u : ℂ)

private lemma P_measurable (n : ℕ) (s : ℂ) {U : ℝ} (hU : u₀ ≤ U) :
    AEStronglyMeasurable (P n s) (volume.restrict (Ioi U)) := by
  have hm := Complex.continuous_ofReal.comp_aestronglyMeasurable
    (tail_integrable.mono_set (Ioi_subset_Ioi hU)).aestronglyMeasurable
  exact (by fun_prop : Continuous (fun u : ℝ =>
    (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)))).aestronglyMeasurable.mul hm

private lemma P_norm (n : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖P n s u‖ = u ^ n * Real.exp (-s.re * u) * ‖f u‖ := by
  simp [P, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, Complex.norm_exp, Complex.mul_re]

private lemma exp_majorant_integrable {U c : ℝ} (hU : u₀ ≤ U) (hc : 0 < c) (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-c * u) *
      (∫ v in Ioi u₀, ‖k v‖)) (Ioi U) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := c)
    (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
  simpa only [IntegrableOn, Real.rpow_one, Real.rpow_natCast] using
    (h.mono_set (Ioi_subset_Ioi (u₀_pos.le.trans hU))).mul_const (∫ v in Ioi u₀, ‖k v‖)

private lemma P_integrable {U : ℝ} (hU : u₀ ≤ U) (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (P n s) (Ioi U) := by
  refine (exp_majorant_integrable hU hs n).mono' (P_measurable n s hU) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu₀ : u₀ ≤ u := hU.trans hu.le
  have hu0 : 0 ≤ u := u₀_pos.le.trans hu₀
  rw [P_norm n s hu0]
  exact mul_le_mul_of_nonneg_left (tail_bound hu₀) (by positivity)

private lemma P_hasDeriv (n : ℕ) (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z => P n z u) (-P (n + 1) s u) s := by
  have h := ((((hasDerivAt_id s).neg).mul_const (u : ℂ)).cexp.const_mul
    ((u : ℂ) ^ n)).mul_const (f u : ℂ)
  convert h using 1 <;> dsimp [P] <;> simp only [pow_succ] <;> ring

private lemma moment_hasDeriv {U : ℝ} (hU : u₀ ≤ U) (n : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z => ∫ u in Ioi U, P n z u)
      (-(∫ u in Ioi U, P (n + 1) s u)) s := by
  have heps : 0 < s.re / 2 := by linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := P n) (F' := fun z u => -P (n + 1) z u)
    (μ := volume.restrict (Ioi U)) (s := {z : ℂ | s.re / 2 < z.re})
    (bound := fun u : ℝ => u ^ (n + 1) * Real.exp (-(s.re / 2) * u) *
      (∫ v in Ioi u₀, ‖k v‖))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith))
    (Eventually.of_forall fun z => P_measurable n z hU) (P_integrable hU n hs)
    (P_measurable (n + 1) s hU).neg ?_ (exp_majorant_integrable hU heps (n + 1))
    (Eventually.of_forall fun u z _ => P_hasDeriv n u z)
  · simpa only [integral_neg] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    have hu₀ : u₀ ≤ u := hU.trans hu.le
    have hu0 : 0 ≤ u := u₀_pos.le.trans hu₀
    rw [norm_neg, P_norm (n + 1) z hu0]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hz.le) hu0)) (by positivity))
      (tail_bound hu₀) (norm_nonneg _) (by positivity)

private lemma L_hasDeriv {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (L U) (-(∫ u in Ioi U, P 1 s u)) s := by
  change HasDerivAt (fun z => ∫ u in Ioi U, Complex.exp (-z * (u : ℂ)) * (f u : ℂ)) _ s
  simpa only [P, Nat.zero_add, pow_zero, one_mul] using moment_hasDeriv hU 0 hs

private lemma Lsecond_hasDeriv {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (deriv (L U)) (∫ u in Ioi U, P 2 s u) s := by
  have h := (moment_hasDeriv hU 1 hs).neg
  simp only [neg_neg] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact (L_hasDeriv hU hz).deriv

private lemma L_analytic {U : ℝ} (hU : u₀ ≤ U) :
    AnalyticOnNhd ℂ (L U) {s | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (L_hasDeriv hU hs).differentiableAt.differentiableWithinAt

private lemma real_tail_ibp {a b : ℝ} (ha : u₀ ≤ a) (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ u in a..b, g u * k u) =
      g b * f b - g a * f a - ∫ u in a..b, deriv g u * f u := by
  have hd : ∀ᵐ u : ℝ, u ∈ Ioi u₀ → deriv f u = k u :=
    (ae_restrict_iff' measurableSet_Ioi).mp (tail_ae_deriv.mono fun _ h => h.deriv)
  have he : (∫ u in a..b, g u * k u) = ∫ u in a..b, g u * deriv f u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with u hu huu
    rw [uIoc_of_le hab] at huu
    rw [hu (lt_of_le_of_lt ha huu.1)]
  exact he.trans (hg.contDiffOn.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    (tail_ac ha hab))

private lemma complex_tail_ibp {a b : ℝ} (ha : u₀ ≤ a) (hab : a ≤ b)
    (g g' : ℝ → ℂ) (hg : ContDiff ℝ 1 g) (hg' : Continuous g')
    (hdg : ∀ u, HasDerivAt g (g' u) u) :
    (∫ u in a..b, g u * (k u : ℂ)) =
      g b * (f b : ℂ) - g a * (f a : ℂ) - ∫ u in a..b, g' u * (f u : ℂ) := by
  have hki : IntervalIntegrable k volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact k_integrable.mono_set (fun u hu => lt_of_le_of_lt ha hu.1)
  have hfi := (tail_ac ha hab).continuousOn.intervalIntegrable (μ := volume)
  have hleft : IntervalIntegrable (fun u => g u * (k u : ℂ)) volume a b := by
    simpa only [Complex.real_smul, mul_comm] using
      hki.smul_continuousOn hg.continuous.continuousOn
  have hright : IntervalIntegrable (fun u => g' u * (f u : ℂ)) volume a b := by
    simpa only [Complex.real_smul, mul_comm] using
      hfi.smul_continuousOn hg'.continuousOn
  have hp (ℓ : ℂ →L[ℝ] ℝ) :
      ℓ (∫ u in a..b, g u * (k u : ℂ)) =
        ℓ (g b * (f b : ℂ) - g a * (f a : ℂ) -
          ∫ u in a..b, g' u * (f u : ℂ)) := by
    rw [← ℓ.intervalIntegral_comp_comm hleft, map_sub, map_sub,
      ← ℓ.intervalIntegral_comp_comm hright]
    have hscl (z : ℂ) (r : ℝ) : ℓ (z * (r : ℂ)) = ℓ z * r := by
      rw [mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]
    simp_rw [hscl]
    have hd (u : ℝ) : deriv (fun v => ℓ (g v)) u = ℓ (g' u) :=
      (ℓ.hasFDerivAt.comp_hasDerivAt u (hdg u)).deriv
    simpa only [hd] using real_tail_ibp ha hab (fun u => ℓ (g u)) (ℓ.contDiff.comp hg)
  exact Complex.ext (hp Complex.reCLM) (hp Complex.imCLM)

private def H (s : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ 2 * Complex.exp (-s * (u : ℂ))

private def Hprime (s : ℂ) (u : ℝ) : ℂ :=
  (2 * (u : ℂ) - s * (u : ℂ) ^ 2) * Complex.exp (-s * (u : ℂ))

private lemma H_hasDeriv (s : ℂ) (u : ℝ) : HasDerivAt (H s) (Hprime s u) u := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := u)).pow 2).mul
    (((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-s)).cexp)
  change HasDerivAt (fun v : ℝ => (v : ℂ) ^ 2 * Complex.exp (-s * (v : ℂ)))
    ((2 * (u : ℂ) - s * (u : ℂ) ^ 2) * Complex.exp (-s * (u : ℂ))) u
  convert h using 1
  · ext v
    simp only [Pi.mul_apply, Pi.pow_apply, Complex.ofRealCLM_apply]
  · norm_num
    ring

private def J (s : ℂ) (u : ℝ) : ℂ := H s u * (k u : ℂ)
private def R (s : ℂ) (u : ℝ) : ℂ := Hprime s u * (f u : ℂ)

private lemma J_eq (s : ℂ) {u : ℝ} (hu : u ≠ 0) :
    J s u = (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ) +
      Complex.exp (-s * (u : ℂ)) * (q u : ℂ) := by
  dsimp [J, H, k]
  push_cast
  have hc : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  field_simp

private lemma R_eq (s : ℂ) (u : ℝ) : R s u = 2 * P 1 s u - s * P 2 s u := by
  dsimp [R, Hprime, P]
  ring

private lemma J_integrable {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (J s) (Ioi U) := by
  obtain ⟨hQ, _, hQ₁, _⟩ := (ThetaLaplaceContinuation.theta_laplace_continuation U
    (u₀_pos.le.trans hU)).2.2.2.1 s hs
  refine (hQ₁.add hQ).congr_fun ?_ measurableSet_Ioi
  intro u hu
  exact (J_eq s (ne_of_gt (u₀_pos.trans_le (hU.trans hu.le)))).symm

private lemma R_integrable {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (R s) (Ioi U) := by
  have hr : IntegrableOn (fun u => 2 * P 1 s u - s * P 2 s u) (Ioi U) :=
    ((P_integrable hU 1 hs).const_mul 2).sub ((P_integrable hU 2 hs).const_mul s)
  refine hr.congr_fun ?_ measurableSet_Ioi
  intro u _
  exact (R_eq s u).symm

private lemma boundary_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun u => H s u * (f u : ℂ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) s.re hs).mul_const
    (∫ v in Ioi u₀, ‖k v‖)
  simp only [Real.rpow_two, zero_mul] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop u₀] with u hu
  change ‖P 2 s u‖ ≤ _
  rw [P_norm 2 s (u₀_pos.le.trans hu)]
  exact mul_le_mul_of_nonneg_left (tail_bound hu) (by positivity)

private lemma improper_ibp {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi U, J s u) =
      -H s U * (f U : ℂ) - ∫ u in Ioi U, R s u := by
  have hleft := intervalIntegral_tendsto_integral_Ioi U (J_integrable hU hs)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hright := ((boundary_tendsto hs).sub
    (tendsto_const_nhds (x := H s U * (f U : ℂ)))).sub
    (intervalIntegral_tendsto_integral_Ioi U (R_integrable hU hs)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  have he : (fun T => ∫ u in U..T, J s u) =ᶠ[atTop]
      (fun T => H s T * (f T : ℂ) - H s U * (f U : ℂ) - ∫ u in U..T, R s u) := by
    filter_upwards [eventually_ge_atTop U] with T hT
    exact complex_tail_ibp hU hT (H s) (Hprime s)
      (by have hc : ContDiff ℝ 1 (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
          exact (hc.pow 2).mul (((contDiff_const (c := -s)).mul hc).cexp))
      (by change Continuous (fun u : ℝ =>
            (2 * (u : ℂ) - s * (u : ℂ) ^ 2) * Complex.exp (-s * (u : ℂ)))
          fun_prop) (H_hasDeriv s)
  have hlim := tendsto_nhds_unique hleft (hright.congr' he.symm)
  simpa only [id_eq, zero_sub, neg_mul] using hlim

private lemma actual_ode {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    s * deriv (deriv (L U)) s + 2 * deriv (L U) s =
      -deriv (Q U) s + Q U s +
        (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-s * (U : ℂ)) := by
  obtain ⟨hQ, _, hQ₁, hdQ⟩ := (ThetaLaplaceContinuation.theta_laplace_continuation U
    (u₀_pos.le.trans hU)).2.2.2.1 s hs
  have hJ : (∫ u in Ioi U, J s u) = -deriv (Q U) s + Q U s := by
    rw [hdQ.deriv, neg_neg, Q, ← integral_add hQ₁ hQ]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact J_eq s (ne_of_gt (u₀_pos.trans_le (hU.trans hu.le)))
  have hR : (∫ u in Ioi U, R s u) =
      2 * (∫ u in Ioi U, P 1 s u) - s * (∫ u in Ioi U, P 2 s u) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((P_integrable hU 1 hs).const_mul 2) ((P_integrable hU 2 hs).const_mul s)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => R_eq s u)
  have hi := improper_ibp hU hs
  rw [hJ, hR] at hi
  rw [(L_hasDeriv hU hs).deriv, (Lsecond_hasDeriv hU hs).deriv]
  dsimp [H] at hi
  linear_combination -hi

private lemma tail_ae_identity :
    ∀ᵐ u ∂volume.restrict (Ioi u₀), u ^ 2 * deriv f u = (u + 1) * q u := by
  filter_upwards [tail_ae_deriv, ae_restrict_mem measurableSet_Ioi] with u hd hu
  rw [hd.deriv, k]
  have hu0 : u ≠ 0 := ne_of_gt (u₀_pos.trans hu)
  field_simp

/-- The actual signed theta tail and its complex Laplace ODE, with its positive
cutoff boundary term retained at every admissible real cutoff. -/
theorem actual_theta_tail_laplace_ode :
    IntegrableOn q (Ioi u₀) ∧ IntegrableOn k (Ioi u₀) ∧
    (∀ U : ℝ, u₀ ≤ U → IntegrableOn (fun t : ℝ => (Chebyshev.theta t - t) *
      D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) (Ioi (Real.exp U))) ∧
    (∀ u : ℝ, f u = F (Real.exp u)) ∧
    IntegrableOn f (Ioi u₀) ∧
    (∀ u : ℝ, u₀ ≤ u → ‖f u‖ ≤ ∫ v in Ioi u₀, ‖k v‖) ∧
    Tendsto f atTop (𝓝 0) ∧
    (∀ a b : ℝ, u₀ ≤ a → a ≤ b → AbsolutelyContinuousOnInterval f a b) ∧
    (∀ᵐ u ∂volume.restrict (Ioi u₀), HasDerivAt f (k u) u ∧
      u ^ 2 * deriv f u = (u + 1) * q u) ∧
    (∀ U : ℝ, u₀ ≤ U → AnalyticOnNhd ℂ (L U) {s | 0 < s.re} ∧
      ∀ s : ℂ, 0 < s.re →
        (∀ n : ℕ, IntegrableOn (fun u : ℝ =>
          (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) (Ioi U)) ∧
        HasDerivAt (L U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (f u : ℂ))) s ∧
        HasDerivAt (deriv (L U))
          (∫ u in Ioi U, (u : ℂ) ^ 2 * Complex.exp (-s * (u : ℂ)) * (f u : ℂ)) s ∧
        s * deriv (deriv (L U)) s + 2 * deriv (L U) s =
          -deriv (Q U) s + Q U s +
            (U : ℂ) ^ 2 * (f U : ℂ) * Complex.exp (-s * (U : ℂ))) := by
  refine ⟨q_integrable, k_integrable, fun _ h => original_integrable h, tail_substitution,
    tail_integrable, fun _ h => tail_bound h, tail_tendsto, fun _ _ h h' => tail_ac h h',
    tail_ae_deriv.and tail_ae_identity, ?_⟩
  intro U hU
  refine ⟨L_analytic hU, fun s hs => ⟨fun n => P_integrable hU n hs, ?_,
    Lsecond_hasDeriv hU hs, actual_ode hU hs⟩⟩
  simpa only [P, pow_one] using L_hasDeriv hU hs

#print axioms actual_theta_tail_laplace_ode

end
end D5.S3.Weil.Mertens.ActualThetaTailLaplace
