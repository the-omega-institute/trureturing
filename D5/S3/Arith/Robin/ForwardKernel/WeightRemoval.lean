/- GID: D5/S3/Arith/Robin/ForwardKernel/WeightRemoval
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/WeightRemoval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Price removal for profiles has negligible mean-square and von Koch pointwise errors. -/

import D5.S3.Arith.Robin.ForwardKernel.WeightControl
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthRegularity
import D5.S3.Arith.Robin.ForwardKernel.MovingIncrementVariance

/-! Removing the price weight from moving integrable profiles. -/

namespace D5.S3.Arith.Robin.ForwardKernel.WeightRemoval

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs VarianceTransfer

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def unweightedResponse (E : ℝ → ℝ) (θ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt x * movingAverage E θ g x

def VonKochBoundFor (E : ℝ → ℝ) : Prop :=
  ∃ C t₀ : ℝ, 0 ≤ C ∧ 3 ≤ t₀ ∧
    ∀ t : ℝ, t₀ ≤ t → |E t| ≤ C * Real.sqrt t * (Real.log t) ^ 2

lemma price_measurable : Measurable (fun p : ℝ × ℝ => priceRatio p.1 p.2) := by
  unfold priceRatio MellinWeightedVariation.weight
  fun_prop

lemma normalized_eq {E g : ℝ → ℝ} {θ x : ℝ} (hx : 0 < x) :
    profileResponse E θ g x / Real.sqrt x =
      (∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
        ∂unitMeasure) / x ^ θ := by
  have hh := (Real.rpow_pos_of_pos hx θ).ne'
  calc
    _ = profileAverage E (fun s => g s * priceRatio x (s * x ^ θ)) (x ^ θ) x := by
      unfold profileResponse profileAverage profilePrimitive
      simp_rw [div_mul_cancel₀ _ hh]
      have he : (fun u => g (u / x ^ θ) * increment E u x * priceRatio x u) =
          (fun u => g (u / x ^ θ) * priceRatio x u * increment E u x) := by
        funext u; ring
      rw [he]
      field_simp [(Real.sqrt_pos.mpr hx).ne']
    _ = _ := by
      rw [profileAverage_eq_unit_integral,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun s => by ring)

lemma local_increment_bound {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (θ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      |increment E (s * x ^ θ) x| ≤ M := by
  have hc : ContinuousOn (fun x : ℝ => x ^ θ) (Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (ha.trans_le hx.1)))
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨M, hM, hMb⟩ := hE.2 a (b + |L|)
  refine ⟨2 * M, by positivity, ?_⟩
  intro x hx s hs
  have hp := Real.rpow_pos_of_pos (ha.trans_le hx.1) θ
  have hpow : x ^ θ ≤ |L| := by
    have := hL x hx
    rw [Real.norm_eq_abs, abs_of_pos hp] at this
    exact this.trans (le_abs_self L)
  have hxE := hMb x ⟨hx.1, by linarith [hx.2, abs_nonneg L]⟩
  have hxu := hMb (x + s * x ^ θ)
    ⟨by nlinarith [hx.1, hs.1], by nlinarith [hx.2, hs.2]⟩
  exact (abs_sub _ _).trans (by linarith)

lemma increment_measurable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) (θ : ℝ) :
    Measurable (fun p : ℝ × ℝ => increment E (p.2 * p.1 ^ θ) p.1) := by
  exact (hE.1.comp (measurable_fst.add
    (measurable_snd.mul (measurable_fst.pow_const θ)))).sub (hE.1.comp measurable_fst)

/-- The normalized price response belongs to L² on compact intervals above three. -/
theorem profileResponse_normalized_memLp {E g : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g) (θ : ℝ)
    {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    MemLp (fun x => profileResponse E θ g x / Real.sqrt x)
      2 (volume.restrict (Ioc a b)) := by
  have ha0 : 0 < a := by linarith
  obtain ⟨M, hM, hMb⟩ := local_increment_bound hE θ ha0 hab
  have hc : ContinuousOn (fun x : ℝ => (x ^ θ)⁻¹) (Icc a b) :=
    (continuousOn_id.rpow_const
      (fun x hx => Or.inl (ne_of_gt (ha0.trans_le hx.1)))).inv₀
        (fun x hx => (Real.rpow_pos_of_pos (ha0.trans_le hx.1) θ).ne')
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hm : Measurable (fun p : ℝ × ℝ =>
      g p.2 * increment E (p.2 * p.1 ^ θ) p.1 * priceRatio p.1 (p.2 * p.1 ^ θ)) :=
    ((hg.1.comp measurable_snd).mul (increment_measurable hE θ)).mul
      (price_measurable.comp (measurable_fst.prodMk
        (measurable_snd.mul (measurable_fst.pow_const θ))))
  have hmeas : Measurable (fun x =>
      (∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
        ∂unitMeasure) / x ^ θ) :=
    (hm.stronglyMeasurable.integral_prod_right').measurable.div (measurable_id.pow_const θ)
  apply MemLp.ae_eq (f := fun x =>
      (∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
        ∂unitMeasure) / x ^ θ) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (normalized_eq (ha0.trans_le hx.1.le)).symm
  · apply MemLp.of_bound hmeas.aestronglyMeasurable (profileL1 g * M * |K|)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
    have hx0 := ha0.trans_le hx'.1
    have hi : ‖∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
        ∂unitMeasure‖ ≤ profileL1 g * M := by
      have hb : ∀ᵐ s ∂unitMeasure,
          ‖g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)‖ ≤ |g s| * M := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        obtain ⟨h0, h1⟩ := WeightControl.price_bounds (ha.trans hx'.1)
          (mul_nonneg hs.1.le (Real.rpow_pos_of_pos hx0 θ).le)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0]
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hMb x hx' s ⟨hs.1.le, hs.2⟩) (abs_nonneg _)) h0).trans
            (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hM) h1)
      simpa only [integral_mul_const, profileL1] using
        norm_integral_le_of_norm_le (hg.2.abs.mul_const M) hb
    rw [div_eq_mul_inv, norm_mul]
    exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((hK x hx').trans (le_abs_self K))
        (mul_nonneg (integral_nonneg (fun s => abs_nonneg (g s))) hM))


private lemma profile_s_integrable {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Integrable (fun s => s * g s) unitMeasure := by
  apply hg.2.bdd_mul (c := 1) measurable_id.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simpa only [Real.norm_eq_abs, id_eq, abs_of_nonneg hs.1.le] using hs.2

private lemma normalized_error_bound {E g : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (θ : ℝ) {x : ℝ} (hx : 4 ≤ x) :
    |profileResponse E θ g x / Real.sqrt x - movingAverage E θ g x| ≤
      4 / x * ∫ s, |s * g s| * |increment E (s * x ^ θ) x| ∂unitMeasure := by
  have hx0 : 0 < x := by linarith
  have hh := Real.rpow_pos_of_pos hx0 θ
  have hD := unit_increment_integrable hE hg.2 (x ^ θ) x
  have hρ : Measurable (fun s => priceRatio x (s * x ^ θ)) :=
    price_measurable.comp (measurable_const.prodMk (measurable_id.mul_const _))
  have hw : Integrable
      (fun s => g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)) unitMeasure := by
    apply hD.mul_bdd hρ.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    obtain ⟨h0, h1⟩ := WeightControl.price_bounds (by linarith : 3 ≤ x)
      (mul_nonneg hs.1.le hh.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hmajor := (unit_increment_integrable hE (profile_s_integrable hg).abs (x ^ θ) x).norm
  have hmajor : Integrable (fun s => |s * g s| * |increment E (s * x ^ θ) x|)
      unitMeasure := by simpa only [Real.norm_eq_abs, abs_mul, abs_abs] using hmajor
  have hi : |∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ) -
      g s * increment E (s * x ^ θ) x ∂unitMeasure| ≤
      (4 * x ^ θ / x) *
        ∫ s, |s * g s| * |increment E (s * x ^ θ) x| ∂unitMeasure := by
    have hb : ∀ᵐ s ∂unitMeasure,
        ‖g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ) -
          g s * increment E (s * x ^ θ) x‖ ≤
        (4 * x ^ θ / x) * (|s * g s| * |increment E (s * x ^ θ) x|) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      obtain ⟨h0, h1⟩ := WeightControl.priceRatio_sub_one hx (mul_nonneg hs.1.le hh.le)
      rw [show g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ) -
          g s * increment E (s * x ^ θ) x =
          (g s * increment E (s * x ^ θ) x) * (priceRatio x (s * x ^ θ) - 1) by ring,
        Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonpos (by linarith : priceRatio x (s * x ^ θ) - 1 ≤ 0)]
      calc
        _ ≤ (|g s| * |increment E (s * x ^ θ) x|) * (4 * (s * x ^ θ) / x) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by rw [abs_mul, abs_of_nonneg hs.1.le]; ring
    simpa only [integral_const_mul, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le (hmajor.const_mul _) hb
  rw [normalized_eq hx0, movingAverage, profileAverage_eq_unit_integral,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← sub_div, ← integral_sub hw hD, abs_div, abs_of_pos hh]
  exact (div_le_div_of_nonneg_right hi hh.le).trans_eq (by field_simp)

private theorem increment_vonKoch_bound {E : ℝ → ℝ} {θ : ℝ}
    (hθ : θ < 1) (hVK : VonKochBoundFor E) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ u ∈ Set.Icc (0 : ℝ) (x ^ θ),
        |E (x + u) - E x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 := by
  obtain ⟨C₀, t₀, hC₀, ht₀, hbound⟩ := hVK
  refine ⟨16 * C₀ + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 t₀)] with x hx u hu
  have hx4 : 4 ≤ x := le_max_left _ _ |>.trans hx
  have hxt : t₀ ≤ x := le_max_right _ _ |>.trans hx
  have hx0 : 0 < x := by linarith
  have hwle : x ^ θ ≤ x := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (x := x) (y := θ)
        (z := (1 : ℝ)) (by linarith) hθ.le)
  have hxu : x + u ≤ 2 * x := by linarith [hu.2, hwle]
  have hxu0 : 0 ≤ x + u := by linarith [hu.1]
  have hybound : |E (x + u)| ≤ C₀ * Real.sqrt (x + u) * (Real.log (x + u)) ^ 2 :=
    hbound (x + u) (by linarith [hu.1])
  have hxbound : |E x| ≤ C₀ * Real.sqrt x * (Real.log x) ^ 2 :=
    hbound x hxt
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogxu : 0 ≤ Real.log (x + u) := Real.log_nonneg (by linarith [hu.1])
  have hlog_le : Real.log (x + u) ≤ 2 * Real.log x := by
    have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    have hlogadd : Real.log (x + u) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith [hu.1]) hxu
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlogadd
    linarith
  have hsqrt_le : Real.sqrt (x + u) ≤ 2 * Real.sqrt x := by
    have hs := Real.sqrt_le_sqrt hxu
    have hs2 : Real.sqrt (2 * x) ≤ 2 * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have htwo : Real.sqrt (2 : ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg x)
    exact hs.trans hs2
  have hprod : Real.sqrt (x + u) * (Real.log (x + u)) ^ 2 ≤
      (2 * Real.sqrt x) * (2 * Real.log x) ^ 2 := by
    gcongr
  have hCprod : C₀ * Real.sqrt (x + u) ≤ C₀ * (2 * Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hsqrt_le hC₀
  have hCprod' : C₀ * Real.sqrt (x + u) * (Real.log (x + u)) ^ 2 ≤
      C₀ * (2 * Real.sqrt x) * (2 * Real.log x) ^ 2 := by
    have hlogsq : (Real.log (x + u)) ^ 2 ≤ (2 * Real.log x) ^ 2 := by
      nlinarith [hlog_le, hlogxu, hlogx]
    exact mul_le_mul hCprod hlogsq (by positivity) (by positivity)
  have hybound' : |E (x + u)| ≤ 8 * C₀ * Real.sqrt x * (Real.log x) ^ 2 := by
    calc
      _ ≤ C₀ * (2 * Real.sqrt x) * (2 * Real.log x) ^ 2 :=
        hybound.trans hCprod'
      _ = 8 * C₀ * Real.sqrt x * (Real.log x) ^ 2 := by ring
  have hdiff := (abs_sub _ _).trans (add_le_add hybound' hxbound)
  have hnonneg : 0 ≤ Real.sqrt x * (Real.log x) ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  nlinarith


/-- Under von Koch, the price-removal error is logarithmic-square times the first absolute profile moment. -/
theorem profile_weight_removal_pointwise {E g : ℝ → ℝ} {θ : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hVK : VonKochBoundFor E) :
    Asymptotics.IsBigO atTop
      (fun x => profileResponse E θ g x - unweightedResponse E θ g x)
      (fun x => (Real.log x) ^ 2 * profileL1 (fun s => s * g s)) := by
  obtain ⟨C, hC, hinc⟩ := increment_vonKoch_bound hθ1 hVK
  rw [Asymptotics.isBigO_iff]
  refine ⟨4 * C, ?_⟩
  filter_upwards [hinc, eventually_ge_atTop (4 : ℝ)] with x hinc hx
  have hx0 : 0 < x := by linarith
  have hh := Real.rpow_pos_of_pos hx0 θ
  have hL : 0 ≤ profileL1 (fun s => s * g s) := integral_nonneg (fun s => abs_nonneg _)
  have hint : (∫ s, |s * g s| * |increment E (s * x ^ θ) x| ∂unitMeasure) ≤
      profileL1 (fun s => s * g s) * (C * Real.sqrt x * (Real.log x) ^ 2) := by
    have hb : ∀ᵐ s ∂unitMeasure,
        ‖|s * g s| * |increment E (s * x ^ θ) x|‖ ≤
          |s * g s| * (C * Real.sqrt x * (Real.log x) ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hinc _
        ⟨mul_nonneg hs.1.le hh.le, mul_le_of_le_one_left hh.le hs.2⟩) (abs_nonneg _)
    have hn := norm_integral_le_of_norm_le
      ((profile_s_integrable hg).abs.mul_const (C * Real.sqrt x * (Real.log x) ^ 2)) hb
    simp only [integral_mul_const, Real.norm_eq_abs] at hn
    exact (le_abs_self _).trans hn
  have hb := (normalized_error_bound hE hg θ hx).trans
    (mul_le_mul_of_nonneg_left hint (by positivity : 0 ≤ 4 / x))
  have he : profileResponse E θ g x - unweightedResponse E θ g x =
      Real.sqrt x * (profileResponse E θ g x / Real.sqrt x - movingAverage E θ g x) := by
    unfold unweightedResponse
    field_simp
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs, abs_of_nonneg hL]
  rw [he, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]
  calc
    _ ≤ Real.sqrt x * (4 / x *
        (profileL1 (fun s => s * g s) * (C * Real.sqrt x * (Real.log x) ^ 2))) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg x)
    _ = _ := by
      have hs := Real.sq_sqrt hx0.le
      field_simp
      ring_nf
      simp only [hs]
      ring

private lemma error_square_le {E g : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (hg : ProfileIntegrable g) (θ : ℝ) {x : ℝ} (hx : 4 ≤ x) :
    (profileResponse E θ g x - unweightedResponse E θ g x) ^ 2 / x ≤
      (16 / x ^ 2) * profileL1 (fun s => s * g s) *
        ∫ s, |s * g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure := by
  have hx0 : 0 < x := by linarith
  obtain ⟨M, hM, hMb⟩ := local_increment_bound hE θ hx0 le_rfl
  have hc := profile_cauchy_schwarz (profile_s_integrable hg).abs
    (k := fun s => |increment E (s * x ^ θ) x|)
    (by simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using
      ((increment_measurable hE θ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.norm)
    hM (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simpa only [abs_abs] using hMb x ⟨le_rfl, le_rfl⟩ s ⟨hs.1.le, hs.2⟩)
  simp only [profileL1, abs_abs, sq_abs] at hc
  have hb := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (by positivity : 0 ≤ 4 / x)
      (integral_nonneg (fun s => by positivity)))).mpr (normalized_error_bound hE hg θ hx)
  rw [sq_abs, mul_pow] at hb
  have he : (profileResponse E θ g x - unweightedResponse E θ g x) ^ 2 / x =
      (profileResponse E θ g x / Real.sqrt x - movingAverage E θ g x) ^ 2 := by
    unfold unweightedResponse
    have hs := Real.sq_sqrt hx0.le
    field_simp
    nlinarith [hs]
  rw [he]
  change _ ≤ profileL1 (fun s => s * g s) * _ at hc
  exact hb.trans (by convert mul_le_mul_of_nonneg_left hc (sq_nonneg (4 / x)) using 1 <;> ring)

private lemma error_integral_bound {E g : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (hg : ProfileIntegrable g) {θ X V : ℝ} (hθ : 0 < θ) (hX : 4 ≤ X)
    (hV : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x in X..(2 * X), increment E (s * x ^ θ) x ^ 2) ≤ V) :
    (∫ x in X..(2 * X),
      (profileResponse E θ g x - unweightedResponse E θ g x) ^ 2 / x) ≤
        (16 / X ^ 2) * profileL1 (fun s => s * g s) ^ 2 * V := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  let μ := volume.restrict (Ioc X (2 * X))
  let L := profileL1 (fun s => s * g s)
  have hL : 0 ≤ L := integral_nonneg (fun s => abs_nonneg _)
  obtain ⟨M, hM, hMb⟩ := local_increment_bound hE θ hX0 hXX
  have hi : Integrable (fun p : ℝ × ℝ =>
      |p.2 * g p.2| * increment E (p.2 * p.1 ^ θ) p.1 ^ 2) (μ.prod unitMeasure) := by
    have hgprod : Integrable (fun p : ℝ × ℝ => |p.2 * g p.2|) (μ.prod unitMeasure) := by
      simpa only [one_mul] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ).mul_prod
          (profile_s_integrable hg).abs
    apply hgprod.mul_bdd ((increment_measurable hE θ).pow_const 2).aestronglyMeasurable
    have hrect : ∀ᵐ p ∂(μ.prod unitMeasure),
        p.1 ∈ Ioc X (2 * X) ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
      dsimp [μ, unitMeasure]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hrect] with p hp
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr
      (hMb p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2 ⟨hp.2.1.le, hp.2.2⟩)
  have hG : Integrable
      (fun x => ∫ s, |s * g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure) μ :=
    hi.integral_prod_left
  have hGbound : (∫ x, ∫ s, |s * g s| * increment E (s * x ^ θ) x ^ 2
      ∂unitMeasure ∂μ) ≤ L * V := by
    rw [integral_integral_swap hi]
    simp_rw [integral_const_mul]
    change _ ≤ (∫ s, |s * g s| ∂unitMeasure) * V
    rw [← integral_mul_const]
    apply integral_mono_ae
    · simpa only [integral_const_mul] using hi.integral_prod_right
    · exact (profile_s_integrable hg).abs.mul_const V
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_le_mul_of_nonneg_left
        (by simpa only [intervalIntegral.integral_of_le hXX] using hV s ⟨hs.1.le, hs.2⟩)
        (abs_nonneg _)
  have hmem := (profileResponse_normalized_memLp hE hg θ (by linarith : 3 ≤ X) hXX).sub
    (MovingLengthRegularity.profileAverage_variable_memLp hE hg
      (measurable_id.pow_const θ) hXX (Real.rpow_pos_of_pos hX0 θ)
      (fun x hx => ⟨Real.rpow_le_rpow hX0.le hx.1 hθ.le,
        Real.rpow_le_rpow (hX0.trans_le hx.1).le hx.2 hθ.le⟩))
  have hf : Integrable
      (fun x => (profileResponse E θ g x / Real.sqrt x - movingAverage E θ g x) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
  have he (x : ℝ) (hx : X ≤ x) :
      (profileResponse E θ g x - unweightedResponse E θ g x) ^ 2 / x =
      (profileResponse E θ g x / Real.sqrt x - movingAverage E θ g x) ^ 2 := by
    have hx0 := hX0.trans_le hx
    have hs := Real.sq_sqrt hx0.le
    unfold unweightedResponse
    field_simp
    nlinarith [hs]
  calc
    _ = ∫ x, (profileResponse E θ g x / Real.sqrt x - movingAverage E θ g x) ^ 2 ∂μ := by
      rw [intervalIntegral.integral_of_le hXX]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact he x hx.1.le
    _ ≤ ∫ x, (16 / X ^ 2) * L *
        (∫ s, |s * g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure) ∂μ := by
      apply integral_mono_ae hf (hG.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [← he x hx.1.le]
      exact (error_square_le hE hg θ (hX.trans hx.1.le)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hX0)
              (pow_le_pow_left₀ hX0.le hx.1.le 2)) hL)
          (integral_nonneg (fun s => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
    _ = (16 / X ^ 2) * L *
        (∫ x, ∫ s, |s * g s| * increment E (s * x ^ θ) x ^ 2 ∂unitMeasure ∂μ) :=
      integral_const_mul _ _
    _ ≤ (16 / X ^ 2) * L * (L * V) :=
      mul_le_mul_of_nonneg_left hGbound (by positivity)
    _ = _ := by ring

/-- The variance band alone makes price removal negligible at the moving mean-square scale. -/
theorem profile_weight_removal_l2 {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Tendsto
      (fun X =>
        (∫ x in X..(2 * X),
          (profileResponse E θ g x - unweightedResponse E θ g x) ^ 2 / x) /
          meanSquareScale θ X)
      atTop (𝓝 0) := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨C, hC, hinc⟩ := MovingIncrementVariance.moving_increment_square_bound hE hB hV
  let L := profileL1 (fun s => s * g s)
  have hdecay : Tendsto (fun X : ℝ => (16 * L ^ 2 * C) * (X ^ (θ - 1)) ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).pow 2
    simpa only [neg_sub, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      h.const_mul (16 * L ^ 2 * C)
  apply squeeze_zero' ?_ ?_ hdecay
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
    have hX0 : 0 < X := by linarith
    apply div_nonneg
    · exact intervalIntegral.integral_nonneg (by linarith)
        (fun x hx => div_nonneg (sq_nonneg _) (by linarith [hx.1]))
    · exact mul_nonneg (Real.rpow_pos_of_pos hX0 _).le
        (Real.log_nonneg (by linarith))
  · filter_upwards [hinc, eventually_ge_atTop (4 : ℝ)] with X hinc hX
    have hX0 : 0 < X := by linarith
    have hlog := Real.log_pos (by linarith : 1 < X)
    have hscale : 0 < meanSquareScale θ X :=
      mul_pos (Real.rpow_pos_of_pos hX0 _) hlog
    have hb := error_integral_bound hE hg hθ0 hX hinc
    apply (div_le_div_of_nonneg_right hb hscale.le).trans_eq
    have he : X ^ (1 - θ) = X / X ^ θ := by
      rw [Real.rpow_sub hX0, Real.rpow_one]
    have he' : X ^ (θ - 1) = X ^ θ / X := by
      rw [Real.rpow_sub hX0, Real.rpow_one]
    dsimp [meanSquareScale]
    rw [he, he']
    dsimp [L]
    field_simp
    <;> ring

end
end D5.S3.Arith.Robin.ForwardKernel.WeightRemoval
