/- GID: D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveAbel
   mirror-E: none(waiver:analytic-arithmetic-inequality)
   anchors: []
   utility: none
   digest: Abel summation and integrated prime-power corrections control the reciprocal-square band. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RobinActualWeightedBound
import D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Set MeasureTheory Filter Finset
open scoped Topology Chebyshev
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
open D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit

namespace D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel

/-- Exact Abel summation for the prime reciprocal-square band. -/
theorem finite_theta_abel {a z : ℝ} (ha : 1 < a) (haz : a ≤ z) :
    (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊z⌋₊).filter Nat.Prime, 1/(p:ℝ)^2) =
    Chebyshev.theta z/(z^2*Real.log z) - Chebyshev.theta a/(a^2*Real.log a) +
    ∫ t in a..z, Chebyshev.theta t*weight 2 t := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log p else 0
  let f : ℝ → ℝ := fun t => 1/(t^2*Real.log t)
  have ha0 : 0 < a := by linarith
  have hc (t : ℝ) : (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, c p) = Chebyshev.theta t := by
    simp only [c, ← sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hd (t : ℝ) (ht : t ∈ Set.Icc a z) : HasDerivAt f (-(weight 2 t)) t := by
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hlt : 0 < Real.log t := Real.log_pos (ha.trans_le ht.1)
    have h := (hasDerivAt_const t (1:ℝ)).div (((hasDerivAt_id t).pow 2).mul (Real.hasDerivAt_log ht0.ne')) (mul_ne_zero (pow_ne_zero 2 ht0.ne') hlt.ne')
    convert h using 1
    · ext; rfl
    · simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
      unfold weight H
      rw [show (2+1:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      field_simp [ht0.ne',hlt.ne']; ring
  have hcont : ContinuousOn (fun t => -weight 2 t) (Set.Icc a z) := by
    intro t ht
    have ht1 : 1 < t := ha.trans_le ht.1
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos ht1
    unfold weight H
    simp_rw [show (2+1:ℝ) = ((3:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    fun_prop (disch := positivity)
  have hi : IntegrableOn (deriv f) (Set.Icc a z) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c ha0.le haz (fun t ht => (hd t ht).differentiableAt) hi
  simp_rw [hc] at habel
  rw [← intervalIntegral.integral_of_le haz] at habel
  have hs : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊z⌋₊, f p * c p) =
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊z⌋₊).filter Nat.Prime, 1/(p:ℝ)^2 := by
    simp only [c, mul_ite, mul_zero, ← sum_filter]
    apply sum_congr rfl
    intro p hp
    have hp' := (mem_filter.mp hp).2
    have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp'.one_lt
    dsimp [f]
    field_simp [(Real.log_pos hp1).ne']
  rw [hs] at habel
  have hint : (∫ t in a..z, deriv f t*Chebyshev.theta t) =
      -(∫ t in a..z, Chebyshev.theta t*weight 2 t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le haz] at ht
    dsimp only
    rw [(hd t ht).deriv]; ring
  rw [hint] at habel
  unfold f at habel
  linear_combination habel

/-- The elementary main tail corresponding to a real power. -/
def B (j r u : ℝ) : ℝ := ∫ v in Set.Ioi u, Real.exp ((r-j)*v)*H j v

private lemma B_integrable {j r u : ℝ} (hj : 0 ≤ j) (hr : r < j) (hu : 0 < u) :
    IntegrableOn (fun v => Real.exp ((r-j)*v)*H j v) (Set.Ioi u) := by
  apply ((integrableOn_exp_mul_Ioi (by linarith : r-j < 0) u).mul_const (H j u)).mono'
  · exact (show ContinuousOn (fun v => Real.exp ((r-j)*v)*H j v) (Set.Ioi u) by
      intro v hv
      have hv0 := hu.trans hv
      unfold H
      fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (H_nonneg hj (hu.trans hv)))]
    exact mul_le_mul_of_nonneg_left (H_antitone hj hu hv.le) (Real.exp_nonneg _)

private lemma primitive_integral {c b u : ℝ} (hc : c < 0) (hu : 0 < u) (hb: 0 ≤ b) :
    (∫ v in Set.Ioi u, Real.exp (c*v)*((-c)*b/v+b/v^2)) = b*Real.exp (c*u)/u := by
  have hi : IntegrableOn (fun v => Real.exp (c*v)*((-c)*b/v+b/v^2)) (Set.Ioi u) := by
    apply ((integrableOn_exp_mul_Ioi hc u).mul_const ((-c)*b/u+b/u^2)).mono'
    · exact (show ContinuousOn (fun v => Real.exp (c*v)*((-c)*b/v+b/v^2)) (Set.Ioi u) by
        intro v hv; have hv0 := hu.trans hv
        fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 := hu.trans hv
      have hc0 : 0 ≤ -c := neg_nonneg.mpr hc.le
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact add_le_add (div_le_div_of_nonneg_left (by positivity) hu hv.le)
        (div_le_div_of_nonneg_left hb (by positivity) (pow_le_pow_left₀ hu.le hv.le 2))
  have hd (v : ℝ) (hv : 0 < v) : HasDerivAt (fun t => -b*Real.exp (c*t)/t)
      (Real.exp (c*v)*((-c)*b/v+b/v^2)) v := by
    have h := ((((hasDerivAt_id v).const_mul c).exp).const_mul (-b)).div (hasDerivAt_id v) hv.ne'
    convert h using 1
    · ext; simp
    · simp only [id_eq]; field_simp [hv.ne']; ring
  have hlim : Tendsto (fun t => -b*Real.exp (c*t)/t) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (c*t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
    have hv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using (he.const_mul (-b)).mul hv
  simpa only [zero_sub,neg_div,neg_mul,neg_neg] using integral_Ioi_of_hasDerivAt_of_tendsto' (fun v hv => hd v (hu.trans_le hv)) hi hlim

/-- Uniform upper main-term bound for every positive prime-power exponent below j. -/
theorem B_upper {j r u : ℝ} (hr0 : 0 ≤ r) (hr : r < j) (hu : 0 < u) :
    B j r u ≤ j/(j-r)*Real.exp ((r-j)*u)/u := by
  let b := j/(j-r)
  have hb : 1 ≤ b := (le_div_iff₀ (sub_pos.mpr hr)).mpr (by linarith)
  have he : -(r-j)*b = j := by dsimp [b]; field_simp [sub_ne_zero.mpr hr.ne']; ring
  have hI := primitive_integral (b:=b) (by linarith : r-j<0) hu (by linarith)
  rw [he] at hI
  rw [← hI]
  unfold B
  have hi : IntegrableOn (fun v => Real.exp ((r-j)*v)*(j/v+b/v^2)) (Set.Ioi u) := by
    apply ((integrableOn_exp_mul_Ioi (by linarith : r-j<0) u).mul_const (j/u+b/u^2)).mono'
    · exact (show ContinuousOn (fun v => Real.exp ((r-j)*v)*(j/v+b/v^2)) (Set.Ioi u) by
        intro v hv; have hv0 := hu.trans hv; fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 := hu.trans hv
      have hj0 : 0 ≤ j := by linarith
      have hb0 : 0 ≤ b := by linarith
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact add_le_add (div_le_div_of_nonneg_left hj0 hu hv.le)
        (div_le_div_of_nonneg_left hb0 (by positivity) (pow_le_pow_left₀ hu.le hv.le 2))
  apply setIntegral_mono_on (B_integrable (by linarith) hr hu) hi measurableSet_Ioi
  intro v hv
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  unfold H
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hb (sq_nonneg _))

/-- Positive power weight, expressed by the elementary logarithmic integral. -/
theorem B_real {j r u : ℝ} (hj : 0 ≤ j) (hr : r < j) (hu : 0 < u) :
    IntegrableOn (fun t => t^r*weight j t) (Set.Ioi (Real.exp u)) ∧
    B j r u = ∫ t in Set.Ioi (Real.exp u), t^r*weight j t := by
  have he (v : ℝ) : Real.exp v • ((Real.exp v)^r*weight j (Real.exp v)) =
      Real.exp ((r-j)*v)*H j v := by
    unfold weight
    simp only [smul_eq_mul,Real.log_exp,← Real.exp_mul,← Real.exp_add,← Real.exp_sub]
    rw [show v * (j+1) = v*j+v by ring]
    calc
      Real.exp v * (Real.exp (v*r)*(H j v / Real.exp (v*j+v))) =
          Real.exp (v+v*r-(v*j+v))*H j v := by
        rw [Real.exp_sub,Real.exp_add v (v*r)]; ring
      _ = _ := by congr 2; ring
  refine ⟨(integrableOn_comp_exp_Ioi _ u).mp ((B_integrable hj hr hu).congr (ae_of_all _ (fun v => (he v).symm))), ?_⟩
  unfold B
  rw [← integral_comp_exp_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi (fun v _ => (he v).symm)

lemma weight_nonneg {j t : ℝ} (hj : 0 ≤ j) (ht : 1 < t) : 0 ≤ weight j t := by
  unfold weight
  exact div_nonneg (H_nonneg hj (Real.log_pos ht)) (Real.rpow_nonneg (by linarith) _)

/-- The exact root substitution, including the logarithmic Jacobian. -/
theorem centered_prime_power_weight {j k x : ℝ} (hk : 0 < k) (hx : 1 < x) :
    (∫ t in Set.Ioi x, (Chebyshev.psi (t^k⁻¹)-t^k⁻¹)*weight j t) =
      (1/k)*J (k*j) (x^k⁻¹) := by
  let g := fun t : ℝ => (Chebyshev.psi (t^k⁻¹)-t^k⁻¹)*weight j t
  let y := x^k⁻¹
  have hx0 : 0 < x := by linarith
  have hy : 0 < y := Real.rpow_pos_of_pos hx0 _
  have h := integral_comp_rpow_Ioi_of_pos' (g:=g) hk hx0.le
  have he (s : ℝ) (hs : s ∈ Set.Ioi y) :
      (k*s^(k-1)) • g (s^k) = (1/k)*((Chebyshev.psi s-s)*weight (k*j) s) := by
    have hs0 := hy.trans hs
    have hroot : (s^k)^k⁻¹ = s := by rw [← Real.rpow_mul hs0.le, mul_inv_cancel₀ hk.ne',Real.rpow_one]
    have hlog : Real.log (s^k) = k*Real.log s := Real.log_rpow hs0 k
    have hH : H j (k*Real.log s) = H (k*j) (Real.log s)/k^2 := by
      unfold H
      by_cases hl : Real.log s = 0
      · simp [hl]
      · field_simp [hk.ne',hl] <;> ring
    have hp : s^(k-1) / (s^k)^(j+1) = 1/s^(k*j+1) := by
      rw [← Real.rpow_mul hs0.le,← Real.rpow_sub hs0, one_div,← Real.rpow_neg hs0.le]
      congr 1 <;> ring
    unfold g weight
    rw [smul_eq_mul,hroot,hlog,hH]
    calc
      _ = (k/k^2)*(Chebyshev.psi s-s)*H (k*j) (Real.log s)*(s^(k-1)/(s^k)^(j+1)) := by ring
      _ = _ := by rw [hp]; field_simp [hk.ne'] <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,← J_eq_integral hy] at h
  exact h.symm

/-- Weighted Chebyshev prime-power deficit. -/
def P (j x : ℝ) : ℝ := ∫ t in Set.Ioi x, (Chebyshev.psi t-Chebyshev.theta t)*weight j t

/-- Actual weighted prime count tail. -/
def T (j x : ℝ) : ℝ := ∫ t in Set.Ioi x, Chebyshev.theta t*weight j t

private lemma theta_weight_integrable {j x : ℝ} (hj : 1 < j) (hx : 1 < x) :
    IntegrableOn (fun t => Chebyshev.theta t*weight j t) (Set.Ioi x) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have h := (B_real (j:=j) (r:=1) (by linarith) hj hl).1
  rw [Real.exp_log hx0] at h
  apply (h.const_mul (Real.log 4)).mono'
  · exact (Chebyshev.theta_mono.measurable.mul (by unfold weight H; fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 := hx.trans ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Chebyshev.theta_nonneg _) (weight_nonneg (by linarith) ht1)),Real.rpow_one]
    exact (mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x ht0.le)
      (weight_nonneg (by linarith) ht1)).trans_eq (by ring)

private lemma psi_root_weight_integrable {j k x : ℝ} (hj : 0 ≤ j) (hk : 0 < k) (hkj : k⁻¹ < j) (hx : 1 < x) :
    IntegrableOn (fun t => Chebyshev.psi (t^k⁻¹)*weight j t) (Set.Ioi x) := by
  have hx0 : 0 < x := by linarith
  have h := (B_real hj hkj (Real.log_pos hx)).1
  rw [Real.exp_log hx0] at h
  apply (h.const_mul (Real.log 4+4)).mono'
  · exact ((Chebyshev.psi_mono.measurable.comp (by fun_prop : Measurable (fun t : ℝ => t^k⁻¹))).mul
      (by unfold weight H; fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 := hx.trans ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Chebyshev.psi_nonneg _) (weight_nonneg hj ht1))]
    exact (mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg ht0.le _))
      (weight_nonneg hj ht1)).trans_eq (by ring)

private lemma psi_weight_integrable {j x : ℝ} (hj : 1 < j) (hx : 1 < x) :
    IntegrableOn (fun t => Chebyshev.psi t*weight j t) (Set.Ioi x) := by
  simpa using psi_root_weight_integrable (j:=j) (k:=1) (by linarith) (by norm_num) (by simpa using hj) hx

private lemma P_integrable {j x : ℝ} (hj : 1 < j) (hx : 1 < x) :
    IntegrableOn (fun t => (Chebyshev.psi t-Chebyshev.theta t)*weight j t) (Set.Ioi x) := by
  apply ((psi_weight_integrable hj hx).sub (theta_weight_integrable hj hx)).congr
  filter_upwards with t
  simp only [Pi.sub_apply]; ring

lemma P_nonneg {j x : ℝ} (hj : 1 < j) (hx : 1 < x) : 0 ≤ P j x := by
  exact setIntegral_nonneg measurableSet_Ioi (fun t ht => mul_nonneg
    (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (weight_nonneg (by linarith) (hx.trans ht)))

lemma T_eq {j x : ℝ} (hj : 1 < j) (hx : 1 < x) :
    T j x = B j 1 (Real.log x) + J j x - P j x := by
  have hx0 : 0 < x := by linarith
  have hB := B_real (j:=j) (r:=1) (by linarith) hj (Real.log_pos hx)
  rw [Real.exp_log hx0] at hB
  have hmain : IntegrableOn (fun t => t*weight j t) (Set.Ioi x) := by simpa using hB.1
  have hJ : IntegrableOn (fun t => (Chebyshev.psi t-t)*weight j t) (Set.Ioi x) := by
    apply ((psi_weight_integrable hj hx).sub hmain).congr
    filter_upwards with t; simp only [Pi.sub_apply]; ring
  rw [J_eq_integral hx0, hB.2]
  simp only [Real.rpow_one]
  unfold T P
  rw [← integral_add hmain hJ]
  have hi : IntegrableOn (fun t => t*weight j t + (Chebyshev.psi t-t)*weight j t) (Set.Ioi x) := hmain.add hJ
  rw [← integral_sub hi (P_integrable hj hx)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)

/-- Each integrated prime-power correction has the same ordinary weighted error at its root. -/
lemma integrated_root {j k x : ℝ} (hj : 1 < j) (hk : 1 ≤ k) (hx : 1 < x) :
    (∫ t in Set.Ioi x, Chebyshev.psi (t^k⁻¹)*weight j t) =
      B j k⁻¹ (Real.log x) + (1/k)*J (k*j) (x^k⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := by linarith
  have hr : k⁻¹ < j := (inv_le_one_of_one_le₀ hk).trans_lt hj
  have hB := B_real (j:=j) (r:=k⁻¹) (by linarith) hr (Real.log_pos hx)
  rw [Real.exp_log hx0] at hB
  have hψ := psi_root_weight_integrable (by linarith : 0 ≤ j) hk0 hr hx
  have hc : IntegrableOn (fun t => (Chebyshev.psi (t^k⁻¹)-t^k⁻¹)*weight j t) (Set.Ioi x) := by
    apply (hψ.sub hB.1).congr
    filter_upwards with t; simp only [Pi.sub_apply]; ring
  rw [hB.2, ← centered_prime_power_weight hk0 hx, ← integral_add hB.1 hc]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)

lemma P_upper_root {j x : ℝ} (hj : 1 < j) (hx : 1 < x) :
    P j x ≤ (B j (2:ℝ)⁻¹ (Real.log x)+(1/2)*J (2*j) (x^(2:ℝ)⁻¹))+
      (B j (3:ℝ)⁻¹ (Real.log x)+(1/3)*J (3*j) (x^(3:ℝ)⁻¹))+
      (B j (5:ℝ)⁻¹ (Real.log x)+(1/5)*J (5*j) (x^(5:ℝ)⁻¹)) := by
  rw [← integrated_root hj (by norm_num : (1:ℝ)≤2) hx,
    ← integrated_root hj (by norm_num : (1:ℝ)≤3) hx,
    ← integrated_root hj (by norm_num : (1:ℝ)≤5) hx]
  have hi (k : ℝ) (hk : 1 ≤ k) := psi_root_weight_integrable (by linarith : 0 ≤ j)
    (by linarith : 0 < k) ((inv_le_one_of_one_le₀ hk).trans_lt hj) hx
  have h2 := hi 2 (by norm_num)
  have h3 := hi 3 (by norm_num)
  have h5 := hi 5 (by norm_num)
  rw [← integral_add h2 h3]
  have h23 : IntegrableOn (fun t => Chebyshev.psi (t^(2:ℝ)⁻¹)*weight j t + Chebyshev.psi (t^(3:ℝ)⁻¹)*weight j t) (Set.Ioi x) := h2.add h3
  rw [← integral_add h23 h5]
  apply setIntegral_mono_on (P_integrable hj hx) ((h2.add h3).add h5) measurableSet_Ioi
  intro t ht
  have h := mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t)
    (weight_nonneg (by linarith : 0 ≤ j) (hx.trans ht))
  simp only [Pi.add_apply]
  linarith only [h]

theorem B_two_lower {u : ℝ} (hu : 0 < u) :
    2*Real.exp (-u)/u-Real.exp (-u)/u^2 ≤ B 2 1 u := by
  let F := fun v : ℝ => Real.exp (-v)/v^2
  have hF : IntegrableOn F (Set.Ioi u) := by
    apply ((integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) u).mul_const (1/u^2)).mono'
    · exact (show ContinuousOn F (Set.Ioi u) by
        intro v hv; have hv0 := hu.trans hv; unfold F; fun_prop (disch := positivity)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (by unfold F; positivity)]
      dsimp [F]; rw [neg_one_mul]
      have hm := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
        (by positivity : 0 < u^2) (pow_le_pow_left₀ hu.le hv.le 2)) (Real.exp_nonneg (-v))
      simpa only [div_eq_mul_inv,one_mul] using hm
  have hI := primitive_integral (c:=(-1)) (b:=2) (by norm_num) hu (by norm_num)
  have hsum : B 2 1 u+(∫ v in Set.Ioi u,F v) = 2*Real.exp (-u)/u := by
    unfold B
    rw [← integral_add (B_integrable (by norm_num : (0:ℝ)≤2) (by norm_num : (1:ℝ)<2) hu) hF]
    rw [neg_one_mul] at hI
    rw [← hI]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    norm_num [H,F]; ring
  have hminor : (∫ v in Set.Ioi u,F v) ≤ Real.exp (-u)/u^2 := by
    have hi := (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) u).mul_const (1/u^2)
    have h := setIntegral_mono_on hF hi measurableSet_Ioi (fun v hv => by
      dsimp [F]; rw [neg_one_mul]
      have hm := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
        (by positivity : 0 < u^2) (pow_le_pow_left₀ hu.le hv.le 2)) (Real.exp_nonneg (-v))
      simpa only [div_eq_mul_inv,one_mul] using hm)
    rw [integral_mul_const,integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0)] at h
    norm_num at h
    simpa only [div_eq_mul_inv,one_mul] using h
  linarith

/-- Exact finite integral as the difference of the genuine infinite tails. -/
lemma theta_interval_as_tail {j a z : ℝ} (hj : 1 < j) (ha : 1 < a) (haz : a ≤ z) :
    (∫ t in a..z, Chebyshev.theta t*weight j t) = T j a-T j z := by
  have hA := theta_weight_integrable hj ha
  have hZ := theta_weight_integrable hj (ha.trans_le haz)
  have h := intervalIntegral.integral_interval_add_Ioi hA hZ
  unfold T
  linarith

/-- Lower finite reciprocal-square sum from rigorous weighted tail bounds. -/
theorem theta_abel_from_tails {a z : ℝ} (ha : 1 < a) (haz : a ≤ z) :
    T 2 a-T 2 z-Real.log 4/(a*Real.log a) ≤
      ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊z⌋₊).filter Nat.Prime, 1/(p:ℝ)^2 := by
  rw [finite_theta_abel ha haz, theta_interval_as_tail (by norm_num) ha haz]
  have ha0 : 0 < a := by linarith
  have hz0 : 0 < z := ha0.trans_le haz
  have hal := Real.log_pos ha
  have h := div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x ha0.le)
    (show 0 ≤ a^2*Real.log a by positivity)
  have he : Real.log 4*a/(a^2*Real.log a) = Real.log 4/(a*Real.log a) := by
    field_simp [ha0.ne', (Real.log_pos ha).ne']
  rw [he] at h
  have htop : 0 ≤ Chebyshev.theta z/(z^2*Real.log z) := by
    have := Real.log_pos (ha.trans_le haz)
    exact div_nonneg (Chebyshev.theta_nonneg _) (by positivity)
  linarith

/-- The normalized upper correction from one of the three prime-power roots. -/
lemma normalized_root_bound (hline : ∀ k : ℕ, (actualZero k).re = 1/2) {k u : ℝ} (hk : 1 ≤ k) (hk5 : k ≤ 5)
    (hu : 0 < u) (hroot : Real.log 2 ≤ u/k) :
    Real.exp ((3/2)*u)*u*(B 2 k⁻¹ u+(1/k)*J (k*2) ((Real.exp u)^k⁻¹)) ≤
      2/(2-k⁻¹)*Real.exp ((k⁻¹-1/2)*u)+k*(1/20)*(2+1/u)*Real.exp (((2*k)⁻¹-1/2)*u) := by
  have hk0 : 0 < k := by linarith
  have hr : k⁻¹ < 2 := (inv_le_one_of_one_le₀ hk).trans_lt (by norm_num)
  have hB := B_upper (inv_nonneg.mpr hk0.le) hr hu
  have hJ := (J_log_bounds hline (j:=k*2) (by linarith) (by linarith) hroot).2
  have he : (Real.exp u)^k⁻¹ = Real.exp (u/k) := by rw [← Real.exp_mul,div_eq_mul_inv]
  rw [← he] at hJ
  have hE : firstLiMass*Real.exp ((1/2-k*2)*(u/k))*H (k*2) (u/k) ≤
      (1/20)*Real.exp ((1/2-k*2)*(u/k))*H (k*2) (u/k) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right firstLiMass_lt_twentieth.le (Real.exp_nonneg _))
      (H_nonneg (by positivity) (div_pos hu hk0))
  have h := mul_le_mul_of_nonneg_left (add_le_add hB
      (mul_le_mul_of_nonneg_left (hJ.trans hE) (by positivity : 0 ≤ 1/k)))
    (show 0 ≤ Real.exp ((3/2)*u)*u by positivity)
  refine h.trans_eq ?_
  rw [mul_add]
  congr 1
  · have hex : Real.exp ((3/2)*u)*Real.exp ((k⁻¹-2)*u) = Real.exp ((k⁻¹-1/2)*u) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = 2/(2-k⁻¹)*(Real.exp ((3/2)*u)*Real.exp ((k⁻¹-2)*u)) := by field_simp [hu.ne'] <;> ring
      _ = _ := by rw [hex]
  · have hex : Real.exp ((3/2)*u)*Real.exp ((1/2-k*2)*(u/k)) = Real.exp (((2*k)⁻¹-1/2)*u) := by
      rw [← Real.exp_add]; congr 1; field_simp [hk0.ne']; ring
    calc
      _ = k*(1/20)*(2+1/u)*(Real.exp ((3/2)*u)*Real.exp ((1/2-k*2)*(u/k))) := by
        unfold H; field_simp [hk0.ne',hu.ne'] <;> ring
      _ = _ := by rw [hex]

/-- Uniform rational power bound from a positive integer exponent. -/
lemma exp_power_bound {u c q : ℝ} {n : ℕ} (hu : Real.log 140 ≤ u) (hc : 0 ≤ c)
    (hq : 0 < q) (hn : 0 < n) (hnum : (n:ℝ)*c = 1 ∨ (n:ℝ)*c = 2 ∨ (n:ℝ)*c = 3)
    (hcert : Real.exp (-(n:ℝ)*c*Real.log 140) ≤ q^n) : Real.exp (-c*u) ≤ q := by
  have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu (show -(n:ℝ)*c ≤ 0 by exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hc))
  have he : (Real.exp (-c*u))^n = Real.exp (-(n:ℝ)*c*u) := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (pow_le_pow_iff_left₀ (Real.exp_nonneg _) hq.le hn.ne').mp (he ▸ (h.trans hcert))

end D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel
