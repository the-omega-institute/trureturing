/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Finite local Abel error and capacity of shrinking logarithmic prime boxes. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
import D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError

/-! Local Abel summation on real-endpoint prime boxes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
open Real Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval primeCount
  theta_error_log_power)
open D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError

private lemma continuousOn_inv_log {y z : ℝ} (hy : 1 < y) :
    ContinuousOn (fun t : ℝ => (log t)⁻¹) (Icc y z) := by
  intro t ht
  have ht1 := hy.trans_le ht.1
  exact (continuousAt_log (by linarith : t ≠ 0)).inv₀ (log_pos ht1).ne'
    |>.continuousWithinAt

/-- The local prime count differs from its logarithmic integral by at most
twice the uniform theta error divided by the logarithm of the lower endpoint. -/
theorem abs_primeInterval_card_sub_integral_le {y z E : ℝ}
    (hy : 2 ≤ y) (hyz : y ≤ z)
    (hE : ∀ t ∈ Icc y z, |Chebyshev.theta t - t| ≤ E) :
    |((primeInterval y z).card : ℝ) - ∫ t in y..z, (log t)⁻¹| ≤ 2 * E / log y := by
  let k : ℝ → ℝ := fun t => (t * log t ^ 2)⁻¹
  let e : ℝ → ℝ := fun t => Chebyshev.theta t - t
  have ht (t : ℝ) (h : t ∈ Icc y z) : 1 < t := by linarith [h.1]
  have hk0 (t : ℝ) (h : t ∈ Icc y z) : 0 ≤ k t := by
    dsimp [k]
    exact inv_nonneg.mpr (mul_nonneg (by linarith [ht t h]) (sq_nonneg _))
  have hkc : ContinuousOn k (Icc y z) := by
    intro t h
    have h0 : t ≠ 0 := by linarith [ht t h]
    have hl := (log_pos (ht t h)).ne'
    exact ((continuousAt_id.mul ((continuousAt_log h0).pow 2)).inv₀
      (mul_ne_zero h0 (pow_ne_zero 2 hl))).continuousWithinAt
  have hki := hkc.intervalIntegrable_of_Icc (μ := volume) hyz
  have hti : IntervalIntegrable (fun t => t * k t) volume y z :=
    (continuousOn_id.mul hkc).intervalIntegrable_of_Icc (μ := volume) hyz
  have hθ (x : ℝ) (hx : 2 ≤ x) :
      IntervalIntegrable (fun t => Chebyshev.theta t * k t) volume 2 x := by
    simpa only [k, div_eq_mul_inv] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
        (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hθlocal := (hθ y hy).symm.trans (hθ z (hy.trans hyz))
  have hinv := (continuousOn_inv_log (by linarith : 1 < y)).intervalIntegrable_of_Icc
    (μ := volume) hyz
  have hei : IntervalIntegrable (fun t => e t * k t) volume y z := by
    simpa only [e, sub_mul] using hθlocal.sub hti
  have hder (t : ℝ) (h : t ∈ uIcc y z) :
      HasDerivAt (fun x : ℝ => (log x)⁻¹) (-k t) t := by
    rw [uIcc_of_le hyz] at h
    have h0 : t ≠ 0 := by linarith [ht t h]
    have hl := (log_pos (ht t h)).ne'
    convert (hasDerivAt_log h0).inv hl using 1
    dsimp [k]
    field_simp
  have hkernel : (∫ t in y..z, k t) = (log y)⁻¹ - (log z)⁻¹ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hki.neg
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hproduct : (∫ t in y..z, ((log t)⁻¹ - t * k t)) =
      z * (log z)⁻¹ - y * (log y)⁻¹ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hinv.sub hti)
    intro t h
    convert (hasDerivAt_id t).mul (hder t h) using 1
    · rfl
    · simp only [id_eq, one_mul]
      ring
  have hcount : ((primeInterval y z).card : ℝ) =
      Chebyshev.theta z * (log z)⁻¹ - Chebyshev.theta y * (log y)⁻¹ +
        ∫ t in y..z, Chebyshev.theta t * k t := by
    rw [Selection.primeInterval_card hyz]
    unfold primeCount
    rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hy,
      Chebyshev.primeCounting_eq_theta_div_log_add_integral (hy.trans hyz)]
    simp only [div_eq_mul_inv, k]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hθ y hy) hθlocal
    dsimp only [k] at hadd
    linarith only [hadd]
  have herror : ((primeInterval y z).card : ℝ) - (∫ t in y..z, (log t)⁻¹) =
      e z * (log z)⁻¹ - e y * (log y)⁻¹ + ∫ t in y..z, e t * k t := by
    rw [hcount]
    simp only [e, sub_mul]
    rw [intervalIntegral.integral_sub hθlocal hti,
      intervalIntegral.integral_sub hinv hti] at *
    linarith only [hproduct]
  have habs : |∫ t in y..z, e t * k t| ≤ E * ((log y)⁻¹ - (log z)⁻¹) := by
    rw [← hkernel, ← intervalIntegral.integral_const_mul]
    apply (intervalIntegral.abs_integral_le_integral_abs hyz).trans
    apply intervalIntegral.integral_mono_on hyz (by simpa only [Real.norm_eq_abs] using hei.norm)
      (hki.const_mul E)
    intro t h
    rw [abs_mul, abs_of_nonneg (hk0 t h)]
    exact mul_le_mul_of_nonneg_right (hE t h) (hk0 t h)
  have hylog : 0 ≤ (log y)⁻¹ := inv_nonneg.mpr (log_pos (ht y ⟨le_rfl, hyz⟩)).le
  have hzlog : 0 ≤ (log z)⁻¹ := inv_nonneg.mpr (log_pos (ht z ⟨hyz, le_rfl⟩)).le
  rw [herror]
  calc
    _ ≤ |e z * (log z)⁻¹ - e y * (log y)⁻¹| + |∫ t in y..z, e t * k t| :=
      abs_add_le _ _
    _ ≤ |e z| * (log z)⁻¹ + |e y| * (log y)⁻¹ +
        E * ((log y)⁻¹ - (log z)⁻¹) := by
      apply add_le_add _ habs
      simpa only [abs_mul, abs_of_nonneg hylog, abs_of_nonneg hzlog, abs_neg, sub_eq_add_neg]
        using (abs_add_le (e z * (log z)⁻¹) (-(e y * (log y)⁻¹)))
    _ ≤ E * (log z)⁻¹ + E * (log y)⁻¹ + E * ((log y)⁻¹ - (log z)⁻¹) :=
      add_le_add_left (add_le_add
        (mul_le_mul_of_nonneg_right (hE z ⟨hyz, le_rfl⟩) hzlog)
        (mul_le_mul_of_nonneg_right (hE y ⟨le_rfl, hyz⟩) hylog)) _
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- An actual half-open moving box has its limiting width as its capacity
on the scale `(P / log P) / (C * (log P) ^ a)`. -/
theorem primeInterval_moving_log_power_capacity {C a u v : ℝ}
    (hC : 0 < C) (ha : 0 < a) (huv : u < v) :
    Tendsto (fun P : ℝ =>
      ((primeInterval (P * exp (u / (C * log P ^ a)))
        (P * exp (v / (C * log P ^ a)))).card : ℝ) /
          ((P / log P) / (C * log P ^ a))) atTop (𝓝 (v - u)) := by
  let s (P : ℝ) := C * log P ^ a
  let b (w P : ℝ) := P * exp (w / s P)
  let d (P : ℝ) := (P / log P) / s P
  let J (P : ℝ) := ∫ t in b u P..b v P, (log t)⁻¹
  let Q (P : ℝ) := ((primeInterval (b u P) (b v P)).card : ℝ)
  change Tendsto (fun P => Q P / d P) atTop (𝓝 (v - u))
  have hs : Tendsto s atTop atTop :=
    ((tendsto_rpow_atTop ha).comp tendsto_log_atTop).const_mul_atTop hC
  have hs0 : Tendsto (fun P => (s P)⁻¹) atTop (𝓝 0) := hs.inv_tendsto_atTop
  have hexp (w : ℝ) : Tendsto (fun P => exp (w / s P)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, exp_zero] using (continuous_exp.tendsto 0).comp (hs.const_div_atTop w)
  have hbox (w : ℝ) : ∀ᶠ P in atTop, b w P ∈ Icc (P / 2) (2 * P) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      (hexp w).eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
      (hexp w).eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with P hP hl hh
    exact ⟨by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hl.le hP,
      by rw [mul_comm 2 P]; exact mul_le_mul_of_nonneg_left hh.le hP⟩
  have hgeom : ∀ᶠ P in atTop,
      0 < P ∧ 0 < log P ∧ 0 < s P ∧ 2 ≤ b u P ∧ b u P ≤ b v P ∧
        Icc (b u P) (b v P) ⊆ Icc (P / 2) (2 * P) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), hs.eventually_gt_atTop 0,
      hbox u, hbox v] with P hP hsP hy hz
    have hP0 : 0 < P := by linarith
    refine ⟨hP0, log_pos (by linarith), hsP, by linarith [hy.1], ?_,
      Icc_subset_Icc hy.1 hz.2⟩
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr
      (div_le_div_of_nonneg_right huv.le hsP.le)) hP0.le
  have hlog (w : ℝ) : Tendsto (fun P => log P / log (b w P)) atTop (𝓝 1) := by
    have hsmall := (hs.const_div_atTop w).mul tendsto_log_atTop.inv_tendsto_atTop
    have hratio := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add hsmall
    simp only [mul_zero, add_zero] at hratio
    have h := hratio.inv₀ (one_ne_zero : (1 : ℝ) ≠ 0)
    simp only [inv_one] at h
    apply h.congr'
    filter_upwards [hgeom] with P hP
    obtain ⟨hP0, hL, _, _, _, _⟩ := hP
    dsimp [b]
    rw [log_mul hP0.ne' (exp_pos _).ne', log_exp]
    have heq : (1 : ℝ) + w / s P * (log P)⁻¹ = (log P + w / s P) / log P := by
      field_simp
    rw [heq, inv_div]
  have hder (w : ℝ) : HasDerivAt (fun t : ℝ => exp (t * w)) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w).exp
  have ht : Tendsto (fun P => (s P)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs0, (hs.eventually_gt_atTop 0).mono
      fun _ h => inv_pos.mpr h⟩
  have hwidth : Tendsto (fun P => (exp (v / s P) - exp (u / s P)) * s P)
      atTop (𝓝 (v - u)) := by
    simpa only [Function.comp_def, zero_add, zero_mul, mul_zero, exp_zero, sub_self, sub_zero, Pi.sub_apply,
      smul_eq_mul, inv_inv, div_eq_mul_inv, mul_comm] using
      ((hder v).sub (hder u)).tendsto_slope_zero_right.comp ht
  have hsides (w : ℝ) : Tendsto (fun P => ((b v P - b u P) / log (b w P)) / d P)
      atTop (𝓝 (v - u)) := by
    have h := hwidth.mul (hlog w)
    simp only [mul_one] at h
    apply h.congr'
    filter_upwards [hgeom] with P hP
    obtain ⟨hP0, hL, hsP, _, _, _⟩ := hP
    dsimp only [b, d]
    rw [div_div_eq_mul_div, div_div_eq_mul_div]
    field_simp
    <;> ring
  have hJ : Tendsto (fun P => J P / d P) atTop (𝓝 (v - u)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hsides v) (hsides u)
    · filter_upwards [hgeom] with P hP
      obtain ⟨hP0, hL, hsP, hy, hyz, _⟩ := hP
      apply div_le_div_of_nonneg_right _ (div_nonneg (div_nonneg hP0.le hL.le) hsP.le)
      have h := intervalIntegral.integral_mono_on (μ := volume) hyz intervalIntegrable_const
        ((continuousOn_inv_log (by linarith : 1 < b u P)).intervalIntegrable_of_Icc hyz)
        (fun t ht => inv_anti₀ (log_pos (by linarith [ht.1]))
          (log_le_log (by linarith [ht.1]) ht.2))
      simpa only [J, intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using h
    · filter_upwards [hgeom] with P hP
      obtain ⟨hP0, hL, hsP, hy, hyz, _⟩ := hP
      apply div_le_div_of_nonneg_right _ (div_nonneg (div_nonneg hP0.le hL.le) hsP.le)
      have h := intervalIntegral.integral_mono_on (μ := volume) hyz
        ((continuousOn_inv_log (by linarith : 1 < b u P)).intervalIntegrable_of_Icc hyz)
        intervalIntegrable_const
        (fun t ht => inv_anti₀ (log_pos (by linarith)) (log_le_log (by linarith) ht.1))
      simpa only [J, intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using h
  obtain ⟨N, hN⟩ := exists_nat_gt a
  have hpt : ∀ᶠ t : ℝ in atTop, |Chebyshev.theta t - t| ≤ t / log t ^ N := by
    filter_upwards [(theta_error_log_power N).def (zero_lt_one : (0 : ℝ) < 1),
      eventually_gt_atTop (1 : ℝ)] with t h ht
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg
      (div_nonneg (by linarith : 0 ≤ t) (pow_nonneg (log_pos ht).le N))] using h
  obtain ⟨T, hT⟩ := eventually_atTop.mp hpt
  let K : ℝ := (2 : ℝ) ^ |(1 : ℝ)| * (2 : ℝ) ^ |-(N : ℝ)|
  have hshell : ∀ᶠ P : ℝ in atTop,
      shellError P ≤ K * P * log P ^ (-(N : ℝ)) := by
    apply (eventually_gt_atTop (max 4 (2 * T))).mono
    intro P hP
    have h := shellError_global_power (σ := 1) (B := -(N : ℝ))
      (K := 1) (Y := T) (by norm_num) (fun t ht _ hl => by
        simpa only [one_mul, rpow_one, rpow_neg hl.le, rpow_natCast, div_eq_mul_inv]
          using hT t ht) P hP
    simpa only [K, one_mul, rpow_one] using h
  have hdecay : Tendsto (fun P : ℝ => log P ^ (a - (N : ℝ))) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hN)).comp tendsto_log_atTop
  have hbound : Tendsto (fun P => (2 * K * C * log P ^ (a - (N : ℝ))) *
      (log P / log (b u P))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hdecay.const_mul (2 * K * C)).mul (hlog u)
  have herr : Tendsto (fun P => |Q P / d P - J P / d P|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hbound
    filter_upwards [hgeom, hshell] with P hP hKP
    obtain ⟨hP0, hL, hsP, hy, hyz, hsub⟩ := hP
    have hd : 0 < d P := div_pos (div_pos hP0 hL) hsP
    have hly : 0 < log (b u P) := log_pos (by linarith)
    have hlocal := abs_primeInterval_card_sub_integral_le hy hyz
      (fun t ht => pointwise_le_shellError hP0.le (hsub ht))
    rw [← sub_div, abs_div, abs_of_pos hd]
    calc
      _ ≤ (2 * shellError P / log (b u P)) / d P :=
        div_le_div_of_nonneg_right hlocal hd.le
      _ ≤ (2 * (K * P * log P ^ (-(N : ℝ))) / log (b u P)) / d P :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKP (by norm_num)) hly.le)
          hd.le
      _ = _ := by
        rw [sub_eq_add_neg, rpow_add hL]
        dsimp only [s, d]
        field_simp
        <;> ring
  have herr' : Tendsto (fun P => Q P / d P - J P / d P) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    simpa only [Real.dist_eq, sub_zero, abs_abs] using (Metric.tendsto_nhds.mp herr) ε hε
  simpa only [sub_add_cancel, zero_add] using herr'.add hJ

end D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
