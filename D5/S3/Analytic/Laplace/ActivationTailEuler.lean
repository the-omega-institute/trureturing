/- GID: D5/S3/Analytic/Laplace/ActivationTailEuler
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/ActivationTailEuler
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Actual activation tails and all-cutoff Euler calculus for measurable L1 sources. -/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual activation tails and Euler calculus for measurable L1 sources above a positive threshold. -/

namespace D5.S3.Analytic.Laplace.ActivationTailEuler

open Real Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The reciprocal logarithmic activation kernel for a real source. -/
def k (q : ℝ → ℝ) (u : ℝ) : ℝ := q u * (u + 1) / u ^ 2

/-- The actual signed Lebesgue tail. -/
def f (q : ℝ → ℝ) (u : ℝ) : ℝ := -(∫ v in Ioi u, k q v)

/-- The actual cutoff transform of the tail. -/
def L (q : ℝ → ℝ) (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) * (f q u : ℂ)

/-- The actual cutoff transform of the source. -/
def Q (q : ℝ → ℝ) (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) * (q u : ℂ)

variable {q : ℝ → ℝ} {u₀ : ℝ}

private lemma k_measurable
    (q_measurable : Measurable q) : Measurable (k q) :=
  ((q_measurable.mul (measurable_id.add_const 1)).div (measurable_id.pow_const 2))

private lemma weight_bound
    (u₀_pos : 0 < u₀) {u : ℝ} (hu : u₀ ≤ u) :
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

private lemma k_integrable
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) : IntegrableOn (k q) (Ioi u₀) := by
  refine (q_integrable.norm.const_mul ((u₀ + 1) / u₀ ^ 2)).mono'
    (k_measurable q_measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [k, show q u * (u + 1) / u ^ 2 = q u * ((u + 1) / u ^ 2) by ring, norm_mul]
  have hw := (weight_bound u₀_pos) hu.le
  have hn : ‖(u + 1) / u ^ 2‖ ≤ (u₀ + 1) / u₀ ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2
  exact (mul_le_mul_of_nonneg_left hn (norm_nonneg (q u))).trans_eq (mul_comm _ _)

private lemma tail_increment
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {a b : ℝ} (ha : u₀ ≤ a) (hb : u₀ ≤ b) :
    (f q) b = (f q) a + ∫ v in a..b, (k q) v := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    ((k_integrable u₀_pos q_measurable q_integrable).mono_set (Ioi_subset_Ioi ha))
    ((k_integrable u₀_pos q_measurable q_integrable).mono_set (Ioi_subset_Ioi hb))
  dsimp [f]
  linarith

private lemma tail_bound
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {u : ℝ} (hu : u₀ ≤ u) :
    ‖(f q) u‖ ≤ ∫ v in Ioi u₀, ‖(k q) v‖ := by
  rw [f, norm_neg]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_set (k_integrable u₀_pos q_measurable q_integrable).norm (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun _ h => lt_of_le_of_lt hu h))

private lemma tail_tendsto : Tendsto (f q) atTop (𝓝 0) := by
  change Tendsto (fun u => -(∫ v in Ioi u, (k q) v)) atTop (𝓝 0)
  simpa only [id_eq, neg_zero] using
    (tendsto_integral_Ioi_zero (f := k q) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)).neg

private lemma tail_ac
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {a b : ℝ} (ha : u₀ ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (f q) a b := by
  have hi : IntervalIntegrable (k q) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (k_integrable u₀_pos q_measurable q_integrable).mono_set (fun v hv => lt_of_le_of_lt ha hv.1)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (f q) a) a b :=
    contDiffOn_const.absolutelyContinuousOnInterval
  apply (hc.add (hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp))).congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact ((tail_increment u₀_pos q_measurable q_integrable) ha (ha.trans hu.1)).symm

private lemma weighted_k_integrable
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) :
    IntegrableOn (fun v : ℝ => (v - u₀) * ‖(k q) v‖) (Ioi u₀) := by
  refine (q_integrable.norm.mul_const (1 + 1 / u₀)).mono'
    ((measurable_id.sub_const u₀).mul (k_measurable q_measurable).norm).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : 0 < v := u₀_pos.trans hv
  have hw := (weight_bound u₀_pos) hv.le
  have hk : ‖(k q) v‖ = ‖q v‖ * ((v + 1) / v ^ 2) := by
    rw [k, show q v * (v + 1) / v ^ 2 = q v * ((v + 1) / v ^ 2) by ring,
      norm_mul, Real.norm_eq_abs ((v + 1) / v ^ 2), abs_of_nonneg hw.1]
  have hcoef : (v - u₀) * ((v + 1) / v ^ 2) ≤ 1 + 1 / u₀ := by
    calc
      _ ≤ v * ((v + 1) / v ^ 2) := mul_le_mul_of_nonneg_right (sub_le_self _ u₀_pos.le) hw.1
      _ = 1 + 1 / v := by field_simp
      _ ≤ 1 + 1 / u₀ := add_le_add le_rfl (one_div_le_one_div_of_le u₀_pos hv.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hv.le) (norm_nonneg _)), hk]
  nlinarith [mul_le_mul_of_nonneg_left hcoef (norm_nonneg (q v))]

private lemma tail_integrable
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) : IntegrableOn (f q) (Ioi u₀) := by
  let G : ℝ × ℝ → ℝ := fun p => if u₀ < p.2 ∧ p.2 ≤ p.1 then (k q) p.1 else 0
  have hGm : Measurable G :=
    ((k_measurable q_measurable).comp measurable_fst).ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)) measurable_const
  have hGe (v : ℝ) : (fun u => G (v, u)) = (Ioc u₀ v).indicator (fun _ => (k q) v) := by
    funext u
    simp [G, Set.indicator_apply]
  have hGi (v : ℝ) : Integrable (fun u => G (v, u)) := by
    rw [hGe]
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have hGn (v : ℝ) (hv : u₀ < v) :
      (∫ u : ℝ, ‖G (v, u)‖) = (v - u₀) * ‖(k q) v‖ := by
    simp_rw [show ∀ u, G (v, u) = (Ioc u₀ v).indicator (fun _ => (k q) v) u from
      fun u => congrFun (hGe v) u]
    simp only [norm_indicator_eq_indicator_norm, integral_indicator measurableSet_Ioc,
      integral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hv.le),
      smul_eq_mul, Measure.restrict_apply_univ]
  have hG : Integrable G ((volume.restrict (Ioi u₀)).prod volume) := by
    apply (integrable_prod_iff hGm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hGi, ?_⟩
    exact (weighted_k_integrable u₀_pos q_measurable q_integrable).congr_fun (fun v hv => (hGn v hv).symm) measurableSet_Ioi
  have hinner {u : ℝ} (hu : u₀ < u) :
      (∫ v in Ioi u₀, G (v, u)) = ∫ v in Ioi u, (k q) v := by
    have he : (fun v => G (v, u)) = (Ici u).indicator (k q) := by
      funext v
      simp [G, hu, Set.indicator_apply]
    rw [he, setIntegral_indicator measurableSet_Ici,
      show Ioi u₀ ∩ Ici u = Ici u from
        inter_eq_right.mpr (fun v hv => lt_of_lt_of_le hu hv), integral_Ici_eq_integral_Ioi]
  refine (hG.integral_prod_right.neg.integrableOn).congr_fun ?_ measurableSet_Ioi
  intro u hu
  change -(∫ v in Ioi u₀, G (v, u)) = (f q) u
  rw [hinner hu]
  rfl

private lemma tail_ae_deriv
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) :
    ∀ᵐ u ∂volume.restrict (Ioi u₀), HasDerivAt (f q) ((k q) u) u := by
  let k₀ := (Ioi u₀).indicator (k q)
  have hi : Integrable k₀ := (integrable_indicator_iff measurableSet_Ioi).mpr (k_integrable u₀_pos q_measurable q_integrable)
  have hp := LocallyIntegrable.ae_hasDerivAt_integral hi.locallyIntegrable
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem measurableSet_Ioi] with u hu huu
  have he : ∀ v ∈ Ioi u₀, (f q) u₀ + ∫ t in u₀..v, k₀ t = (f q) v := by
    intro v hv
    rw [(tail_increment u₀_pos q_measurable q_integrable) le_rfl hv.le]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [uIoc_of_le hv.le] at ht
    exact Set.indicator_of_mem ht.1 (k q)
  have hd := (hasDerivAt_const u ((f q) u₀)).add (hu u₀)
  rw [zero_add, show k₀ u = (k q) u from Set.indicator_of_mem huu (k q)] at hd
  exact hd.congr_of_eventuallyEq
    (Filter.EventuallyEq.symm (Filter.eventually_of_mem (isOpen_Ioi.mem_nhds huu) he))

private def P (q : ℝ → ℝ) (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)) * ((f q) u : ℂ)

private lemma P_measurable
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) (n : ℕ) (s : ℂ) {U : ℝ} (hU : u₀ ≤ U) :
    AEStronglyMeasurable ((P q) n s) (volume.restrict (Ioi U)) := by
  have hm := Complex.continuous_ofReal.comp_aestronglyMeasurable
    ((tail_integrable u₀_pos q_measurable q_integrable).mono_set (Ioi_subset_Ioi hU)).aestronglyMeasurable
  exact (by fun_prop : Continuous (fun u : ℝ =>
    (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)))).aestronglyMeasurable.mul hm

private lemma P_norm (n : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖(P q) n s u‖ = u ^ n * Real.exp (-s.re * u) * ‖(f q) u‖ := by
  simp [P, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, Complex.norm_exp, Complex.mul_re]

private lemma exp_majorant_integrable
    (u₀_pos : 0 < u₀) {U c : ℝ} (hU : u₀ ≤ U) (hc : 0 < c) (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-c * u) *
      (∫ v in Ioi u₀, ‖(k q) v‖)) (Ioi U) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := c)
    (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
  simpa only [IntegrableOn, Real.rpow_one, Real.rpow_natCast] using
    (h.mono_set (Ioi_subset_Ioi (u₀_pos.le.trans hU))).mul_const (∫ v in Ioi u₀, ‖(k q) v‖)

private lemma P_integrable
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn ((P q) n s) (Ioi U) := by
  refine ((exp_majorant_integrable (q := q) (u₀ := u₀) u₀_pos) hU hs n).mono' ((P_measurable u₀_pos q_measurable q_integrable) n s hU) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu₀ : u₀ ≤ u := hU.trans hu.le
  have hu0 : 0 ≤ u := u₀_pos.le.trans hu₀
  rw [(P_norm (q := q)) n s hu0]
  exact mul_le_mul_of_nonneg_left ((tail_bound u₀_pos q_measurable q_integrable) hu₀) (by positivity)

private lemma P_hasDeriv (n : ℕ) (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z => (P q) n z u) (-(P q) (n + 1) s u) s := by
  have h := ((((hasDerivAt_id s).neg).mul_const (u : ℂ)).cexp.const_mul
    ((u : ℂ) ^ n)).mul_const ((f q) u : ℂ)
  convert h using 1 <;> dsimp [P] <;> simp only [pow_succ] <;> ring

private lemma moment_hasDeriv
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) (n : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z => ∫ u in Ioi U, (P q) n z u)
      (-(∫ u in Ioi U, (P q) (n + 1) s u)) s := by
  have heps : 0 < s.re / 2 := by linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := (P q) n) (F' := fun z u => -(P q) (n + 1) z u)
    (μ := volume.restrict (Ioi U)) (s := {z : ℂ | s.re / 2 < z.re})
    (bound := fun u : ℝ => u ^ (n + 1) * Real.exp (-(s.re / 2) * u) *
      (∫ v in Ioi u₀, ‖(k q) v‖))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith))
    (Eventually.of_forall fun z => (P_measurable u₀_pos q_measurable q_integrable) n z hU) ((P_integrable u₀_pos q_measurable q_integrable) hU n hs)
    ((P_measurable u₀_pos q_measurable q_integrable) (n + 1) s hU).neg ?_ ((exp_majorant_integrable (q := q) (u₀ := u₀) u₀_pos) hU heps (n + 1))
    (Eventually.of_forall fun u z _ => (P_hasDeriv (q := q)) n u z)
  · simpa only [integral_neg] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    have hu₀ : u₀ ≤ u := hU.trans hu.le
    have hu0 : 0 ≤ u := u₀_pos.le.trans hu₀
    rw [norm_neg, (P_norm (q := q)) (n + 1) z hu0]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (neg_le_neg hz.le) hu0)) (by positivity))
      ((tail_bound u₀_pos q_measurable q_integrable) hu₀) (norm_nonneg _) (by positivity)

private lemma L_hasDeriv
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt ((L q) U) (-(∫ u in Ioi U, (P q) 1 s u)) s := by
  change HasDerivAt (fun z => ∫ u in Ioi U, Complex.exp (-z * (u : ℂ)) * ((f q) u : ℂ)) _ s
  simpa only [P, Nat.zero_add, pow_zero, one_mul] using (moment_hasDeriv u₀_pos q_measurable q_integrable) hU 0 hs

private lemma Lsecond_hasDeriv
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (deriv ((L q) U)) (∫ u in Ioi U, (P q) 2 s u) s := by
  have h := ((moment_hasDeriv u₀_pos q_measurable q_integrable) hU 1 hs).neg
  simp only [neg_neg] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact ((L_hasDeriv u₀_pos q_measurable q_integrable) hU hz).deriv

private lemma L_analytic
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) :
    AnalyticOnNhd ℂ ((L q) U) {s | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact ((L_hasDeriv u₀_pos q_measurable q_integrable) hU hs).differentiableAt.differentiableWithinAt

private lemma real_tail_ibp
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {a b : ℝ} (ha : u₀ ≤ a) (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ u in a..b, g u * (k q) u) =
      g b * (f q) b - g a * (f q) a - ∫ u in a..b, deriv g u * (f q) u := by
  have hd : ∀ᵐ u : ℝ, u ∈ Ioi u₀ → deriv (f q) u = (k q) u :=
    (ae_restrict_iff' measurableSet_Ioi).mp ((tail_ae_deriv u₀_pos q_measurable q_integrable).mono fun _ h => h.deriv)
  have he : (∫ u in a..b, g u * (k q) u) = ∫ u in a..b, g u * deriv (f q) u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with u hu huu
    rw [uIoc_of_le hab] at huu
    rw [hu (lt_of_le_of_lt ha huu.1)]
  exact he.trans (hg.contDiffOn.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    ((tail_ac u₀_pos q_measurable q_integrable) ha hab))

private lemma complex_tail_ibp
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {a b : ℝ} (ha : u₀ ≤ a) (hab : a ≤ b)
    (g g' : ℝ → ℂ) (hg : ContDiff ℝ 1 g) (hg' : Continuous g')
    (hdg : ∀ u, HasDerivAt g (g' u) u) :
    (∫ u in a..b, g u * ((k q) u : ℂ)) =
      g b * ((f q) b : ℂ) - g a * ((f q) a : ℂ) - ∫ u in a..b, g' u * ((f q) u : ℂ) := by
  have hki : IntervalIntegrable (k q) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (k_integrable u₀_pos q_measurable q_integrable).mono_set (fun u hu => lt_of_le_of_lt ha hu.1)
  have hfi := ((tail_ac u₀_pos q_measurable q_integrable) ha hab).continuousOn.intervalIntegrable (μ := volume)
  have hleft : IntervalIntegrable (fun u => g u * ((k q) u : ℂ)) volume a b := by
    simpa only [Complex.real_smul, mul_comm] using
      hki.smul_continuousOn hg.continuous.continuousOn
  have hright : IntervalIntegrable (fun u => g' u * ((f q) u : ℂ)) volume a b := by
    simpa only [Complex.real_smul, mul_comm] using
      hfi.smul_continuousOn hg'.continuousOn
  have hp (ℓ : ℂ →L[ℝ] ℝ) :
      ℓ (∫ u in a..b, g u * ((k q) u : ℂ)) =
        ℓ (g b * ((f q) b : ℂ) - g a * ((f q) a : ℂ) -
          ∫ u in a..b, g' u * ((f q) u : ℂ)) := by
    rw [← ℓ.intervalIntegral_comp_comm hleft, map_sub, map_sub,
      ← ℓ.intervalIntegral_comp_comm hright]
    have hscl (z : ℂ) (r : ℝ) : ℓ (z * (r : ℂ)) = ℓ z * r := by
      rw [mul_comm, ← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]
    simp_rw [hscl]
    have hd (u : ℝ) : deriv (fun v => ℓ (g v)) u = ℓ (g' u) :=
      (ℓ.hasFDerivAt.comp_hasDerivAt u (hdg u)).deriv
    simpa only [hd] using (real_tail_ibp u₀_pos q_measurable q_integrable) ha hab (fun u => ℓ (g u)) (ℓ.contDiff.comp hg)
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

private def J (q : ℝ → ℝ) (s : ℂ) (u : ℝ) : ℂ := H s u * ((k q) u : ℂ)

private def R (q : ℝ → ℝ) (s : ℂ) (u : ℝ) : ℂ := Hprime s u * ((f q) u : ℂ)

private lemma J_eq (s : ℂ) {u : ℝ} (hu : u ≠ 0) :
    (J q) s u = (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ) +
      Complex.exp (-s * (u : ℂ)) * (q u : ℂ) := by
  dsimp [J, H, k]
  push_cast
  have hc : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  field_simp

private lemma R_eq (s : ℂ) (u : ℝ) : (R q) s u = 2 * (P q) 1 s u - s * (P q) 2 s u := by
  dsimp [R, Hprime, P]
  ring

private def B (q : ℝ → ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-s * (u : ℂ)) * (q u : ℂ)

private lemma B_measurable (q_measurable : Measurable q) (s : ℂ) :
    Measurable (B q s) :=
  (by fun_prop : Measurable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))).mul
    (Complex.continuous_ofReal.measurable.comp q_measurable)

private lemma B_norm (s : ℂ) (u : ℝ) :
    ‖B q s u‖ = Real.exp (-s.re * u) * ‖q u‖ := by
  simp [B, Complex.norm_exp, Complex.mul_re]

private lemma source_integrable (u₀_pos : 0 < u₀) (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀))
    {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (B q s) (Ioi U) := by
  refine (q_integrable.mono_set (Ioi_subset_Ioi hU)).norm.mono'
    (B_measurable q_measurable s).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := u₀_pos.le.trans (hU.trans hu.le)
  rw [B_norm]
  have he : Real.exp (-s.re * u) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu0)
  exact (mul_le_mul_of_nonneg_right he (norm_nonneg (q u))).trans_eq (one_mul _)

/-- Uniform first-moment multiplier bound; the source itself need not be bounded. -/
private lemma first_exp_bound {c : ℝ} (hc : 0 < c) (u : ℝ) :
    u * Real.exp (-c * u) ≤ Real.exp (-1) / c := by
  apply (le_div_iff₀ hc).mpr
  calc
    (u * Real.exp (-c * u)) * c = (c * u) * Real.exp (-(c * u)) := by
      simp only [neg_mul]
      ring
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one (c * u)

private lemma B_hasDeriv (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z => B q z u) (-((u : ℂ) * B q s u)) s := by
  have h := ((((hasDerivAt_id s).neg).mul_const (u : ℂ)).cexp).mul_const (q u : ℂ)
  convert h using 1 <;> dsimp [B] <;> ring

private lemma Q_hasDeriv (u₀_pos : 0 < u₀) (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀))
    {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))
      (Ioi U) ∧
    HasDerivAt (Q q U)
      (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))) s := by
  have heps : 0 < s.re / 2 := by linarith
  have hb : IntegrableOn (fun u : ℝ => Real.exp (-1) / (s.re / 2) * ‖q u‖)
      (Ioi U) :=
    (q_integrable.mono_set (Ioi_subset_Ioi hU)).norm.const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := B q) (F' := fun z u => -((u : ℂ) * B q z u))
    (μ := volume.restrict (Ioi U)) (s := {z : ℂ | s.re / 2 < z.re})
    (bound := fun u : ℝ => Real.exp (-1) / (s.re / 2) * ‖q u‖)
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by dsimp; linarith))
    (Eventually.of_forall fun z =>
      (B_measurable q_measurable z).aestronglyMeasurable.restrict)
    (source_integrable u₀_pos q_measurable q_integrable hU hs)
    (((by fun_prop : Measurable (fun u : ℝ => (u : ℂ))).mul
      (B_measurable q_measurable s)).neg.aestronglyMeasurable.restrict) ?_ hb
    (Eventually.of_forall fun u z _ => B_hasDeriv u z)
  · constructor
    · have hi : IntegrableOn (fun u : ℝ => (u : ℂ) * B q s u) (Ioi U) :=
        integrable_neg_iff.mp h.1
      simpa only [B, mul_assoc] using hi
    · unfold Q
      simpa only [B, integral_neg, mul_assoc] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    have hu0 : 0 ≤ u := u₀_pos.le.trans (hU.trans hu.le)
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu0, B_norm]
    calc
      u * (Real.exp (-z.re * u) * ‖q u‖) =
          (u * Real.exp (-z.re * u)) * ‖q u‖ := by ring
      _ ≤ (u * Real.exp (-(s.re / 2) * u)) * ‖q u‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hu0
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (neg_le_neg hz.le) hu0)
      _ ≤ Real.exp (-1) / (s.re / 2) * ‖q u‖ :=
        mul_le_mul_of_nonneg_right (first_exp_bound heps u) (norm_nonneg _)

private lemma J_integrable
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn ((J q) s) (Ioi U) := by
  have hQ := (source_integrable u₀_pos q_measurable q_integrable) hU hs
  have hQ₁ := ((Q_hasDeriv u₀_pos q_measurable q_integrable) hU hs).1
  refine (hQ₁.add hQ).congr_fun ?_ measurableSet_Ioi
  intro u hu
  exact ((J_eq (q := q)) s (ne_of_gt (u₀_pos.trans_le (hU.trans hu.le)))).symm

private lemma R_integrable
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn ((R q) s) (Ioi U) := by
  have hr : IntegrableOn (fun u => 2 * (P q) 1 s u - s * (P q) 2 s u) (Ioi U) :=
    (((P_integrable u₀_pos q_measurable q_integrable) hU 1 hs).const_mul 2).sub (((P_integrable u₀_pos q_measurable q_integrable) hU 2 hs).const_mul s)
  refine hr.congr_fun ?_ measurableSet_Ioi
  intro u _
  exact ((R_eq (q := q)) s u).symm

private lemma boundary_tendsto
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun u => H s u * ((f q) u : ℂ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) s.re hs).mul_const
    (∫ v in Ioi u₀, ‖(k q) v‖)
  simp only [Real.rpow_two, zero_mul] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop u₀] with u hu
  change ‖(P q) 2 s u‖ ≤ _
  rw [(P_norm (q := q)) 2 s (u₀_pos.le.trans hu)]
  exact mul_le_mul_of_nonneg_left ((tail_bound u₀_pos q_measurable q_integrable) hu) (by positivity)

private lemma improper_ibp
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi U, (J q) s u) =
      -H s U * ((f q) U : ℂ) - ∫ u in Ioi U, (R q) s u := by
  have hleft := intervalIntegral_tendsto_integral_Ioi U ((J_integrable u₀_pos q_measurable q_integrable) hU hs)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hright := (((boundary_tendsto u₀_pos q_measurable q_integrable) hs).sub
    (tendsto_const_nhds (x := H s U * ((f q) U : ℂ)))).sub
    (intervalIntegral_tendsto_integral_Ioi U ((R_integrable u₀_pos q_measurable q_integrable) hU hs)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  have he : (fun T => ∫ u in U..T, (J q) s u) =ᶠ[atTop]
      (fun T => H s T * ((f q) T : ℂ) - H s U * ((f q) U : ℂ) - ∫ u in U..T, (R q) s u) := by
    filter_upwards [eventually_ge_atTop U] with T hT
    exact (complex_tail_ibp u₀_pos q_measurable q_integrable) hU hT (H s) (Hprime s)
      (by have hc : ContDiff ℝ 1 (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
          exact (hc.pow 2).mul (((contDiff_const (c := -s)).mul hc).cexp))
      (by change Continuous (fun u : ℝ =>
            (2 * (u : ℂ) - s * (u : ℂ) ^ 2) * Complex.exp (-s * (u : ℂ)))
          fun_prop) (H_hasDeriv s)
  have hlim := tendsto_nhds_unique hleft (hright.congr' he.symm)
  simpa only [id_eq, zero_sub, neg_mul] using hlim

private lemma actual_ode
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) {U : ℝ} (hU : u₀ ≤ U) {s : ℂ} (hs : 0 < s.re) :
    s * deriv (deriv ((L q) U)) s + 2 * deriv ((L q) U) s =
      -deriv ((Q q) U) s + (Q q) U s +
        (U : ℂ) ^ 2 * ((f q) U : ℂ) * Complex.exp (-s * (U : ℂ)) := by
  have hQ := (source_integrable u₀_pos q_measurable q_integrable) hU hs
  obtain ⟨hQ₁, hdQ⟩ := (Q_hasDeriv u₀_pos q_measurable q_integrable) hU hs
  have hJ : (∫ u in Ioi U, (J q) s u) = -deriv ((Q q) U) s + (Q q) U s := by
    rw [hdQ.deriv, neg_neg]
    change _ = _ + ∫ u in Ioi U, B q s u
    rw [← integral_add hQ₁ hQ]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact (J_eq (q := q)) s (ne_of_gt (u₀_pos.trans_le (hU.trans hu.le)))
  have hR : (∫ u in Ioi U, (R q) s u) =
      2 * (∫ u in Ioi U, (P q) 1 s u) - s * (∫ u in Ioi U, (P q) 2 s u) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (((P_integrable u₀_pos q_measurable q_integrable) hU 1 hs).const_mul 2) (((P_integrable u₀_pos q_measurable q_integrable) hU 2 hs).const_mul s)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => (R_eq (q := q)) s u)
  have hi := (improper_ibp u₀_pos q_measurable q_integrable) hU hs
  rw [hJ, hR] at hi
  rw [((L_hasDeriv u₀_pos q_measurable q_integrable) hU hs).deriv, ((Lsecond_hasDeriv u₀_pos q_measurable q_integrable) hU hs).deriv]
  dsimp [H] at hi
  linear_combination -hi

private lemma tail_ae_identity
    (u₀_pos : 0 < u₀)
    (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) :
    ∀ᵐ u ∂volume.restrict (Ioi u₀), u ^ 2 * deriv (f q) u = (u + 1) * q u := by
  filter_upwards [(tail_ae_deriv u₀_pos q_measurable q_integrable), ae_restrict_mem measurableSet_Ioi] with u hd hu
  rw [hd.deriv, k]
  have hu0 : u ≠ 0 := ne_of_gt (u₀_pos.trans hu)
  field_simp

/-- Actual-tail calculus, including the all-cutoff Euler identity on Re(s)>0.
The hypotheses concern only the real source on the initial positive half-line. -/
theorem actual_tail_laplace_ode
    (u₀_pos : 0 < u₀) (q_measurable : Measurable q)
    (q_integrable : IntegrableOn q (Ioi u₀)) :
    IntegrableOn (k q) (Ioi u₀) ∧
    IntegrableOn (f q) (Ioi u₀) ∧
    (∀ u : ℝ, u₀ ≤ u → ‖f q u‖ ≤ ∫ v in Ioi u₀, ‖k q v‖) ∧
    Tendsto (f q) atTop (𝓝 0) ∧
    (∀ a b : ℝ, u₀ ≤ a → a ≤ b → AbsolutelyContinuousOnInterval (f q) a b) ∧
    (∀ᵐ u ∂volume.restrict (Ioi u₀), HasDerivAt (f q) (k q u) u ∧
      u ^ 2 * deriv (f q) u = (u + 1) * q u) ∧
    (∀ U : ℝ, u₀ ≤ U → AnalyticOnNhd ℂ (L q U) {s | 0 < s.re} ∧
      IntegrableOn q (Ioi U) ∧
      ∀ s : ℂ, 0 < s.re →
        (∀ n : ℕ, IntegrableOn (fun u : ℝ =>
          (u : ℂ) ^ n * Complex.exp (-s * (u : ℂ)) * (f q u : ℂ)) (Ioi U)) ∧
        HasDerivAt (L q U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (f q u : ℂ))) s ∧
        HasDerivAt (deriv (L q U))
          (∫ u in Ioi U, (u : ℂ) ^ 2 * Complex.exp (-s * (u : ℂ)) * (f q u : ℂ)) s ∧
        IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (q u : ℂ)) (Ioi U) ∧
        IntegrableOn (fun u : ℝ =>
          (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ)) (Ioi U) ∧
        HasDerivAt (Q q U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-s * (u : ℂ)) * (q u : ℂ))) s ∧
        s * deriv (deriv (L q U)) s + 2 * deriv (L q U) s =
          -deriv (Q q U) s + Q q U s +
            (U : ℂ) ^ 2 * (f q U : ℂ) * Complex.exp (-s * (U : ℂ))) := by
  refine ⟨k_integrable u₀_pos q_measurable q_integrable,
    tail_integrable u₀_pos q_measurable q_integrable,
    fun _ h => tail_bound u₀_pos q_measurable q_integrable h,
    tail_tendsto, fun _ _ h h' => tail_ac u₀_pos q_measurable q_integrable h h',
    (tail_ae_deriv u₀_pos q_measurable q_integrable).and
      (tail_ae_identity u₀_pos q_measurable q_integrable), ?_⟩
  intro U hU
  refine ⟨L_analytic u₀_pos q_measurable q_integrable hU,
    q_integrable.mono_set (Ioi_subset_Ioi hU), fun s hs => ?_⟩
  obtain ⟨hQ₁, hdQ⟩ := Q_hasDeriv u₀_pos q_measurable q_integrable hU hs
  refine ⟨fun n => P_integrable u₀_pos q_measurable q_integrable hU n hs, ?_,
    Lsecond_hasDeriv u₀_pos q_measurable q_integrable hU hs,
    source_integrable u₀_pos q_measurable q_integrable hU hs, hQ₁, hdQ,
    actual_ode u₀_pos q_measurable q_integrable hU hs⟩
  simpa only [P, pow_one] using L_hasDeriv u₀_pos q_measurable q_integrable hU hs

#print axioms actual_tail_laplace_ode

end
end D5.S3.Analytic.Laplace.ActivationTailEuler
