/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Cancellation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/Cancellation
   mirror-E: none(waiver:analytic-inequality)
   anchors: [mathlib/module/Mathlib.NumberTheory.AbelSummation]
   utility: none
   digest: Harmonic cancellation yields a quadratic tail bound for the actual epsilon density. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail.Arithmetic

/-! Exact Abel cancellation for the literal harmonic tail. The signed floor
phase is integrated before taking absolute values. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

private def phaseDensity (t : ℝ) : ℝ := (1 / 2 - Int.fract t) / t ^ 2
private def primitiveDensity (t : ℝ) : ℝ := harmonicPrimitive t / t ^ 2

private lemma primitive_measurable : Measurable harmonicPrimitive := by
  have hH : Measurable H := by
    have he : H = fun x => (harmonic ⌊x⌋₊ : ℝ) := funext H_harmonic
    rw [he]
    exact (measurable_of_countable (fun n : ℕ => (harmonic n : ℝ))).comp Nat.measurable_floor
  change Measurable (fun x : ℝ => x * (H x - Real.log x - gamma) +
    Int.fract x - 1 / 2)
  fun_prop

private lemma phase_bound {t : ℝ} (ht : 1 ≤ t) :
    |phaseDensity t| ≤ 1 / t ^ 2 := by
  have hf0 := Int.fract_nonneg t
  have hf1 := Int.fract_lt_one t
  rw [phaseDensity, abs_div, abs_of_nonneg (sq_nonneg t)]
  gcongr
  rw [abs_le]
  constructor <;> linarith

private lemma phase_integrable : IntegrableOn phaseDensity (Ioi (1 : ℝ)) := by
  have hm : Measurable phaseDensity := by
    change Measurable (fun t : ℝ => (1 / 2 - Int.fract t) / t ^ 2)
    fun_prop
  apply (inv_sq_integrable zero_lt_one).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using phase_bound ht.le

private lemma primitive_integrable : IntegrableOn primitiveDensity (Ioi (1 : ℝ)) := by
  have hm : Measurable primitiveDensity := primitive_measurable.div (by fun_prop)
  apply ((inv_sq_integrable zero_lt_one).const_mul 4).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, primitiveDensity, abs_div, abs_of_nonneg (sq_nonneg t)]
  have ht1 : 1 < t := ht
  have h := harmonicPrimitive_bound ht.le
  have hi : 1 / t ≤ (1 : ℝ) := (div_le_one (by linarith [ht1])).mpr ht.le
  calc
    _ ≤ (4 / t) / t ^ 2 := by gcongr
    _ ≤ 4 * (1 / t ^ 2) := by
      rw [mul_one_div]
      gcongr
      simpa only [div_eq_mul_inv, mul_one, one_mul] using
        mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4)

private lemma epsilon_density_split (t : ℝ) :
    epsilonDensity t = primitiveDensity t + phaseDensity t := by
  dsimp [epsilonDensity, primitiveDensity, harmonicPrimitive, phaseDensity]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
    ring

private lemma floor_inverse_integral {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t ^ 2) = H x - (⌊x⌋₊ : ℝ) / x := by
  let c : ℕ → ℝ := fun n => if n = 0 then 0 else 1
  have hp (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = (⌊t⌋₊ : ℝ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    have hs : (∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, c k) =
        ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [c, if_neg (Finset.mem_Ioc.mp hk).1.ne']
    simp only [c, if_pos rfl, zero_add, hs]
    simp
  have hd (t : ℝ) (ht : t ∈ Icc (1 : ℝ) x) :
      HasDerivAt (fun u : ℝ => u⁻¹) (-(1 / t ^ 2)) t := by
    convert (hasDerivAt_id t).inv (by linarith [ht.1] : t ≠ 0) using 1 <;>
      first | rfl | (simp only [id_eq, one_div]; ring)
  have hi : IntegrableOn (deriv (fun u : ℝ => u⁻¹)) (Icc (1 : ℝ) x) := by
    have hc : ContinuousOn (fun t : ℝ => -(1 / t ^ 2)) (Icc (1 : ℝ) x) := by
      fun_prop (disch := intro t ht; nlinarith [ht.1])
    exact hc.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_integral_mul₀ c (by simp [c]) x
    (fun t ht => (hd t ht).differentiableAt) hi
  have hs (k : ℕ) : (k : ℝ)⁻¹ * c k = (k : ℝ)⁻¹ := by
    by_cases hk : k = 0 <;> simp [c, hk]
  simp only [hs, hp] at ha
  change H x = x⁻¹ * (⌊x⌋₊ : ℝ) -
    ∫ t in Ioc (1 : ℝ) x, deriv (fun u : ℝ => u⁻¹) t * (⌊t⌋₊ : ℝ) at ha
  have he : (∫ t in Ioc (1 : ℝ) x, deriv (fun u : ℝ => u⁻¹) t * (⌊t⌋₊ : ℝ)) =
      -(∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t ^ 2) := by
    rw [intervalIntegral.integral_of_le hx, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv (fun u : ℝ => u⁻¹) t * (⌊t⌋₊ : ℝ) = -((⌊t⌋₊ : ℝ) / t ^ 2)
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    ring
  rw [he] at ha
  simpa only [div_eq_mul_inv, mul_comm] using (by linarith only [ha] :
    (∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t ^ 2) = H x - x⁻¹ * (⌊x⌋₊ : ℝ))

private lemma phase_interval_identity {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, phaseDensity t) =
      harmonicPrimitive x / x - harmonicPrimitive 1 := by
  have hx0 : 0 < x := by linarith
  have hip : IntervalIntegrable phaseDensity volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      (phase_integrable.mono_set Ioc_subset_Ioi_self)
  have hii : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x :=
    (by
      have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Icc (1 : ℝ) x) := by
        fun_prop (disch := intro t ht; linarith [ht.1])
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hc.integrableOn_Icc)
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      ((inv_sq_integrable zero_lt_one).mono_set Ioc_subset_Ioi_self)
  have hif : IntervalIntegrable (fun t : ℝ => (⌊t⌋₊ : ℝ) / t ^ 2) volume 1 x := by
    apply ((hip.add hii).sub (hi2.const_mul (1 / 2 : ℝ))).congr
    intro t ht
    have ht0 : 0 < t := by rw [uIoc_of_le hx] at ht; linarith [ht.1]
    have hf : Int.fract t = t - (⌊t⌋₊ : ℝ) := by
      rw [Int.fract, ← natCast_floor_eq_intCast_floor ht0.le]
    dsimp [phaseDensity]
    rw [hf]
    field_simp
    ring
  have he : (∫ t in (1 : ℝ)..x, phaseDensity t) =
      (∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t ^ 2) -
      (∫ t in (1 : ℝ)..x, t⁻¹) +
      (1 / 2 : ℝ) * ∫ t in (1 : ℝ)..x, 1 / t ^ 2 := by
    rw [← intervalIntegral.integral_sub hif hii, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hif.sub hii) (hi2.const_mul _)]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 < t := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    have hf : Int.fract t = t - (⌊t⌋₊ : ℝ) := by
      rw [Int.fract, ← natCast_floor_eq_intCast_floor ht0.le]
    dsimp [phaseDensity]
    rw [hf]
    field_simp
    ring
  have h2 : (∫ t in (1 : ℝ)..x, 1 / t ^ 2) = 1 - 1 / x := by
    have hd (t : ℝ) (ht : t ∈ uIcc (1 : ℝ) x) :
        HasDerivAt (fun u : ℝ => -u⁻¹) (1 / t ^ 2) t := by
      have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
      convert ((hasDerivAt_id t).inv ht0).neg using 1 <;>
        first | rfl | (simp only [id_eq, one_div]; ring)
    simpa only [inv_one, neg_neg, sub_neg_eq_add, one_div, sub_eq_add_neg, add_comm] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi2)
  rw [he, floor_inverse_integral hx, integral_inv_of_pos zero_lt_one hx0,
    div_one, h2]
  have hf : Int.fract x = x - (⌊x⌋₊ : ℝ) := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor hx0.le]
  have hH1 : H 1 = 1 := by rw [H_harmonic]; norm_num [harmonic]
  dsimp [harmonicPrimitive, epsilon]
  rw [hf, hH1]
  norm_num
  field_simp
  ring

private lemma primitive_ratio_tendsto :
    Tendsto (fun x : ℝ => harmonicPrimitive x / x) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ => 4 / x ^ 2)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < x)]
    calc
      _ ≤ (4 / x) / x := by gcongr; exact harmonicPrimitive_bound hx
      _ = 4 / x ^ 2 := by ring
  · simpa only [div_eq_mul_inv, inv_pow, zero_pow two_ne_zero, mul_zero] using
      (tendsto_inv_atTop_zero.pow 2).const_mul (4 : ℝ)

private lemma phase_tail_identity {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioi x, phaseDensity t) = -harmonicPrimitive x / x := by
  have htotal : (∫ t in Ioi (1 : ℝ), phaseDensity t) = -harmonicPrimitive 1 := by
    apply tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 1 phase_integrable tendsto_id)
    have hlim := primitive_ratio_tendsto.sub_const (harmonicPrimitive 1)
    simp only [zero_sub] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (phase_interval_identity hy).symm
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi phase_integrable hx
  rw [htotal, phase_interval_identity hx] at hsplit
  rw [neg_div]
  linarith

/-- The actual harmonic tail gains a full power by cancellation, uniformly in x. -/
theorem T_epsilon_quadratic_bound {x : ℝ} (hx : 1 ≤ x) :
    |T_epsilon x| ≤ 8 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hip := primitive_integrable.mono_set (Ioi_subset_Ioi hx)
  have hit := phase_integrable.mono_set (Ioi_subset_Ioi hx)
  have hid : T_epsilon x = (∫ t in Ioi x, primitiveDensity t) -
      harmonicPrimitive x / x := by
    rw [T_epsilon]
    simp_rw [epsilon_density_split]
    rw [integral_add hip hit, phase_tail_identity hx]
    ring
  have hm : (∫ t in Ioi x, |primitiveDensity t|) ≤ (4 / x) * (1 / x) := by
    rw [← inv_sq_integral hx0, ← integral_const_mul]
    apply setIntegral_mono_on hip.abs ((inv_sq_integrable hx0).const_mul _) measurableSet_Ioi
    intro t ht
    rw [primitiveDensity, abs_div, abs_of_nonneg (sq_nonneg t)]
    have h := harmonicPrimitive_bound (hx.trans ht.le)
    have hi : 4 / t ≤ 4 / x := by gcongr; exact ht.le
    calc
      _ ≤ (4 / x) / t ^ 2 := by gcongr; exact h.trans hi
      _ = _ := by ring
  have hr : |harmonicPrimitive x / x| ≤ 4 / x ^ 2 := by
    rw [abs_div, abs_of_pos hx0]
    calc
      _ ≤ (4 / x) / x := by gcongr; exact harmonicPrimitive_bound hx
      _ = _ := by ring
  rw [hid]
  calc
    _ ≤ |∫ t in Ioi x, primitiveDensity t| + |harmonicPrimitive x / x| := abs_sub _ _
    _ ≤ (∫ t in Ioi x, |primitiveDensity t|) + 4 / x ^ 2 :=
      add_le_add (abs_integral_le_integral_abs) hr
    _ ≤ 8 / x ^ 2 := by
      have he : (4 / x) * (1 / x) = 4 / x ^ 2 := by ring
      rw [he] at hm
      simp only [div_eq_mul_inv] at hm ⊢
      linarith

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
