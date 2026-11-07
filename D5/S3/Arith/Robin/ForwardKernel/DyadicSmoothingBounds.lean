/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Increment square bounds control dyadic smoothing blocks and their derivatives. -/

import D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingIdentities

/-! Bounds for double averages on intervals with room for all forward translations. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingBounds

open Set MeasureTheory Filter
open VarianceTransferDefs VarianceTransfer CrossExponentDefs AveragingRegularity
open DyadicSmoothingIdentities

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma continuous_lbm {f : ℝ → ℝ} (hf : Continuous f) :
    LocallyBoundedMeasurable f := by
  refine ⟨hf.measurable, fun a b => ?_⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hf.norm).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun x hx =>
    (hM (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩

private lemma increment_lbm {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E) (u : ℝ) :
    LocallyBoundedMeasurable (increment E u) := by
  refine ⟨(hE.1.comp (measurable_id.add_const u)).sub hE.1, fun a b => ?_⟩
  obtain ⟨M, hM, hb⟩ := hE.2 (a + u) (b + u)
  obtain ⟨N, hN, hc⟩ := hE.2 a b
  exact ⟨M + N, add_nonneg hM hN, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hb _ ⟨by linarith [hx.1], by linarith [hx.2]⟩) (hc x hx))⟩

private lemma lbm_memLp {f : ℝ → ℝ} (hf : LocallyBoundedMeasurable f) (a b : ℝ) :
    MemLp f 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨M, _, hM⟩ := hf.2 a b
  apply MemLp.of_bound hf.1.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hM x ⟨hx.1.le, hx.2⟩

private lemma square_integrable {f : ℝ → ℝ} (hf : LocallyBoundedMeasurable f) (a b : ℝ) :
    IntervalIntegrable (fun x => f x ^ 2) volume a b := by
  rw [intervalIntegrable_iff]
  exact (lbm_memLp hf (min a b) (max a b)).integrable_sq

private lemma l2_mono {f : ℝ → ℝ} (hf : LocallyBoundedMeasurable f)
    {a b c d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    intervalL2 a b f ≤ intervalL2 c d f :=
  Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval hca hab hbd
    (Eventually.of_forall fun _ => sq_nonneg _) (square_integrable hf c d))

private lemma l2_linear {f g : ℝ → ℝ} (hf : LocallyBoundedMeasurable f)
    (hg : LocallyBoundedMeasurable g) {a b : ℝ} (hab : a ≤ b) (c d : ℝ) :
    intervalL2 a b (fun x => c * f x + d * g x) ≤
      |c| * intervalL2 a b f + |d| * intervalL2 a b g := by
  have h := lpNorm_add_le ((lbm_memLp hf a b).const_smul c)
    (g := d • g) (by norm_num : (1 : ENNReal) ≤ 2)
  rw [lpNorm_const_smul, lpNorm_const_smul,
    VarianceTransfer.lpNorm_two_eq_intervalL2 hab hf.1.aestronglyMeasurable,
    VarianceTransfer.lpNorm_two_eq_intervalL2 hab hg.1.aestronglyMeasurable] at h
  have hn := VarianceTransfer.lpNorm_two_eq_intervalL2 hab
    ((hf.1.const_mul c).add (hg.1.const_mul d)).aestronglyMeasurable
  change lpNorm (fun x => c * f x + d * g x) 2 _ = _ at hn
  have he : c • f + d • g = fun x => c * f x + d * g x := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [he, hn] at h
  simpa [intervalL2, Pi.add_apply, Real.norm_eq_abs] using h

private lemma average_pointwise {u : ℝ → ℝ} (hu : LocallyBoundedMeasurable u)
    {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |windowAverage R u x| ≤ intervalL2 x (x + R) u / Real.sqrt R := by
  have hi := (locallyBoundedMeasurable_intervalIntegrable hu x (x + R)).comp_add_left x
  have hi2 := (square_integrable hu x (x + R)).comp_add_left x
  have hcs := interval_cauchy_schwarz hR (by simpa using hi) (by simpa using hi2)
  have ht := intervalIntegral.integral_comp_add_left (fun y => u y ^ 2) x
    (a := 0) (b := R)
  simp only [add_zero] at ht
  rw [ht] at hcs
  have hs := Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (show x ≤ x + R by linarith) (fun y => sq_nonneg (u y)))
  have hr := Real.sq_sqrt hR.le
  have hrp := Real.sqrt_pos.mpr hR
  apply (le_div_iff₀ hrp).mpr
  have hsq : (|windowAverage R u x| * Real.sqrt R) ^ 2 ≤
      (intervalL2 x (x + R) u) ^ 2 := by
    unfold windowAverage intervalL2
    rw [mul_pow, sq_abs, div_pow, hr, hs]
    exact (by
      calc
        _ = (∫ r in (0 : ℝ)..R, u (x + r)) ^ 2 / R := by field_simp
        _ ≤ _ := (div_le_iff₀ hR).mpr (by nlinarith [hcs]))
  exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsq

private lemma average_l2 {u : ℝ → ℝ} (hu : LocallyBoundedMeasurable u)
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b) :
    intervalL2 a b (windowAverage R u) ≤ intervalL2 a (b + R) u := by
  have hprod : Integrable (fun p : ℝ × ℝ => u (p.1 + p.2) ^ 2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (0 : ℝ) R))) := by
    obtain ⟨M, hM, hb⟩ := hu.2 a (b + R)
    refine ⟨((hu.1.comp (measurable_fst.add measurable_snd)).pow_const 2).aestronglyMeasurable,
      .of_bounded (C := M ^ 2) ?_⟩
    have hm : ∀ᵐ p ∂((volume.restrict (Ioc a b)).prod
        (volume.restrict (Ioc (0 : ℝ) R))), p ∈ Ioc a b ×ˢ Ioc (0 : ℝ) R := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hm] with p hp
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hb _ ⟨by linarith [hp.1.1, hp.2.1],
        by linarith [hp.1.2, hp.2.2]⟩) 2
  have hinner : IntervalIntegrable (fun x => ∫ t in (0 : ℝ)..R, u (x + t) ^ 2)
      volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hR.le] using hprod.integral_prod_left
  have hpoint (x : ℝ) : windowAverage R u x ^ 2 ≤
      (∫ t in (0 : ℝ)..R, u (x + t) ^ 2) / R := by
    have hc := interval_cauchy_schwarz hR
      (by simpa using (locallyBoundedMeasurable_intervalIntegrable hu x (x + R)).comp_add_left x)
      (by simpa using (square_integrable hu x (x + R)).comp_add_left x)
    unfold windowAverage
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hR) hR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hR.le]
  apply Real.sqrt_le_sqrt
  have hle := intervalIntegral.integral_mono_on hab
    (square_integrable (continuous_lbm (windowAverage_continuous hu hR)) a b)
    (hinner.div_const R) (fun x _ => hpoint x)
  rw [intervalIntegral.integral_div] at hle
  have hswap : (∫ x in a..b, ∫ t in (0 : ℝ)..R, u (x + t) ^ 2) =
      ∫ t in (0 : ℝ)..R, ∫ x in a..b, u (x + t) ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hR.le]
    exact integral_integral_swap hprod
  rw [hswap] at hle
  have hbnd : (∫ t in (0 : ℝ)..R, ∫ x in a..b, u (x + t) ^ 2) ≤
      R * ∫ x in a..(b + R), u x ^ 2 := by
    apply le_trans (intervalIntegral.integral_mono_on
      (g := fun _ => ∫ x in a..(b + R), u x ^ 2) hR.le
      (by rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
          simpa only [IntegrableOn, intervalIntegral.integral_of_le hab] using
            hprod.integral_prod_right)
      intervalIntegrable_const ?_) (by simp)
    intro t ht
    rw [intervalIntegral.integral_comp_add_right (fun y => u y ^ 2)]
    exact intervalIntegral.integral_mono_interval (by linarith [ht.1])
      (by linarith) (by linarith [ht.2])
      (Eventually.of_forall fun _ => sq_nonneg _) (square_integrable hu a (b + R))
  exact hle.trans ((div_le_iff₀ hR).mpr (by nlinarith [hbnd]))

private lemma l2_scale {f : ℝ → ℝ} (hf : Measurable f) {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    intervalL2 a b (fun x => c * f x) = |c| * intervalL2 a b f := by
  rw [← VarianceTransfer.lpNorm_two_eq_intervalL2 hab
      (hf.const_mul c).aestronglyMeasurable,
    ← VarianceTransfer.lpNorm_two_eq_intervalL2 hab hf.aestronglyMeasurable]
  have he : c • f = fun x => c * f x := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  have hn := lpNorm_const_smul c f (volume.restrict (Ioc a b)) (p := 2)
  rw [he] at hn
  simpa [Real.norm_eq_abs] using hn

private lemma double_l2 {u : ℝ → ℝ} (hu : LocallyBoundedMeasurable u)
    {R a b L U : ℝ} (hR : 0 < R) (hab : a ≤ b) (hLa : L ≤ a) (hbU : b + 2 * R ≤ U) :
    intervalL2 a b (doubleAverage R u) ≤ intervalL2 L U u := by
  exact (average_l2 (continuous_lbm (windowAverage_continuous hu hR)) hR hab).trans
    ((average_l2 hu hR (by linarith : a ≤ b + R)).trans
      (l2_mono hu hLa (by linarith) (by linarith)))

private lemma double_abs {u : ℝ → ℝ} (hu : LocallyBoundedMeasurable u)
    {R x L U : ℝ} (hR : 0 < R) (hLx : L ≤ x) (hxU : x + 2 * R ≤ U) :
    |doubleAverage R u x| ≤ intervalL2 L U u / Real.sqrt R := by
  exact (average_pointwise (continuous_lbm (windowAverage_continuous hu hR)) hR x).trans
    (div_le_div_of_nonneg_right
      ((average_l2 hu hR (by linarith : x ≤ x + R)).trans
        (l2_mono hu hLx (by linarith) (by linarith))) (Real.sqrt_nonneg _))

private lemma deriv_average_eq {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R : ℝ} (hR : 0 < R) :
    deriv (doubleAverage R E) = fun x => (1 / R) * windowAverage R (increment E R) x := by
  funext x
  rw [(doubleAverage_hasDerivAt hE hR x).deriv]
  ring

private lemma deriv_average_l2 {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R a b L U : ℝ} (hR : 0 < R) (hab : a ≤ b) (hLa : L ≤ a) (hbU : b + R ≤ U) :
    intervalL2 a b (deriv (doubleAverage R E)) ≤ intervalL2 L U (increment E R) / R := by
  rw [deriv_average_eq hE hR, l2_scale
    (windowAverage_continuous (increment_lbm hE R) hR).measurable hab,
    abs_of_pos (one_div_pos.mpr hR), one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right
    ((average_l2 (increment_lbm hE R) hR hab).trans
      (l2_mono (increment_lbm hE R) hLa (by linarith) hbU)) hR.le

private lemma deriv_average_abs {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R x L U : ℝ} (hR : 0 < R) (hLx : L ≤ x) (hxU : x + R ≤ U) :
    |deriv (doubleAverage R E) x| ≤ intervalL2 L U (increment E R) / (R * Real.sqrt R) := by
  rw [deriv_average_eq hE hR, abs_mul, abs_of_pos (one_div_pos.mpr hR)]
  have h := (average_pointwise (increment_lbm hE R) hR x).trans
    (div_le_div_of_nonneg_right (l2_mono (increment_lbm hE R) hLx
      (by linarith) hxU) (Real.sqrt_nonneg _))
  convert mul_le_mul_of_nonneg_left h (one_div_nonneg.mpr hR.le) using 1; ring

private lemma fixed_scale_bounds {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {R a b L U K : ℝ} (hR : 0 < R) (hab : a ≤ b) (hLa : L ≤ a)
    (hbU : b + 2 * R ≤ U) (hK : 0 ≤ K)
    (hinc : intervalL2 L U (increment E R) ≤ K)
    (hinc2 : intervalL2 L U (increment E (2 * R)) ≤ K) :
    intervalL2 a b (smoothingBlock R E) ≤ K ∧
    intervalL2 a b (deriv (smoothingBlock R E)) ≤ 2 * K / R ∧
    (∀ x ∈ Icc a b, |smoothingBlock R E x| ≤ K / Real.sqrt R) ∧
    intervalL2 a b (deriv (doubleAverage R E)) ≤ K / R ∧
    (∀ x ∈ Icc a b, |deriv (doubleAverage R E) x| ≤ K / (R * Real.sqrt R)) := by
  have hR2 : 0 < 2 * R := by positivity
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hc1 := (doubleAverage_contDiff (increment_lbm hE R) hR).continuous
  have hc2 := (doubleAverage_contDiff (increment_lbm hE (2 * R)) hR).continuous
  have hB : smoothingBlock R E = fun x =>
      -(1 / 2 : ℝ) * doubleAverage R (increment E R) x +
        -(1 / 4 : ℝ) * doubleAverage R (increment E (2 * R)) x := by
    funext x
    rw [smoothingBlock_eq_averaged_increments hE hR]
    ring
  simp only [neg_mul] at hB
  have hdB : deriv (smoothingBlock R E) = fun x =>
      deriv (doubleAverage R E) x - deriv (doubleAverage (2 * R) E) x := by
    funext x
    exact ((doubleAverage_hasDerivAt hE hR x).sub
      (doubleAverage_hasDerivAt hE hR2 x)).deriv.trans (by
        rw [(doubleAverage_hasDerivAt hE hR x).deriv,
          (doubleAverage_hasDerivAt hE hR2 x).deriv])
  have hz1 := (deriv_average_l2 hE hR hab hLa (by linarith : b + R ≤ U)).trans
    (div_le_div_of_nonneg_right hinc hR.le)
  have hz2 := (deriv_average_l2 hE hR2 hab hLa hbU).trans
    (div_le_div_of_nonneg_right hinc2 hR2.le)
  refine ⟨?_, ?_, ?_, hz1, ?_⟩
  · rw [hB]
    have h := l2_linear (continuous_lbm hc1) (continuous_lbm hc2) hab
      (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ))
    norm_num at h
    have h1 := (double_l2 (increment_lbm hE R) hR hab hLa hbU).trans hinc
    have h2 := (double_l2 (increment_lbm hE (2 * R)) hR hab hLa hbU).trans hinc2
    linarith
  · rw [hdB]
    have h := l2_linear
      (continuous_lbm ((doubleAverage_contDiff hE hR).continuous_deriv le_rfl))
      (continuous_lbm ((doubleAverage_contDiff hE hR2).continuous_deriv le_rfl)) hab 1 (-1)
    simp only [one_mul, neg_one_mul, abs_one, abs_neg] at h
    apply h.trans
    apply le_trans (add_le_add hz1 hz2)
    apply (le_div_iff₀ hR).mpr
    field_simp
    nlinarith
  · intro x hx
    rw [hB]
    have h1 := (double_abs (increment_lbm hE R) hR (hLa.trans hx.1)
      (by linarith [hx.2] : x + 2 * R ≤ U)).trans
      (div_le_div_of_nonneg_right hinc hs.le)
    have h2 := (double_abs (increment_lbm hE (2 * R)) hR (hLa.trans hx.1)
      (by linarith [hx.2] : x + 2 * R ≤ U)).trans
      (div_le_div_of_nonneg_right hinc2 hs.le)
    have h := abs_add_le (-(1 / 2 : ℝ) * doubleAverage R (increment E R) x)
      (-(1 / 4 : ℝ) * doubleAverage R (increment E (2 * R)) x)
    rw [abs_mul, abs_mul] at h
    norm_num at h
    have hnon : 0 ≤ K / Real.sqrt R := div_nonneg hK hs.le
    dsimp only
    linarith
  · intro x hx
    exact (deriv_average_abs hE hR (hLa.trans hx.1) (by linarith [hx.2])).trans
      (div_le_div_of_nonneg_right hinc (by positivity))

/-- Uniform increment bounds give all five smoothing estimates throughout the scale range. -/
theorem dyadic_smoothing_bounds {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {h k A a b L U : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hab : a ≤ b) (hLa : L ≤ a)
    (hmargin : b + 4 * k ≤ U)
    (hinc : ∀ u ∈ Icc h (8 * k), intervalL2 L U (increment E u) ≤ A * Real.sqrt u) :
    ∀ R ∈ Icc h (2 * k),
      intervalL2 a b (smoothingBlock R E) ≤ 2 * A * Real.sqrt R ∧
      intervalL2 a b (deriv (smoothingBlock R E)) ≤ 4 * A / Real.sqrt R ∧
      (∀ x ∈ Icc a b, |smoothingBlock R E x| ≤ 2 * A) ∧
      intervalL2 a b (deriv (doubleAverage R E)) ≤ 2 * A / Real.sqrt R ∧
      (∀ x ∈ Icc a b, |deriv (doubleAverage R E) x| ≤ 2 * A / R) := by
  intro R hR
  have hp : 0 < R := hh.trans_le hR.1
  have hk : 0 < k := by linarith [hR.2]
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  have hcomp : Real.sqrt (2 * R) ≤ 2 * Real.sqrt R := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by nlinarith⟩
  have hi1 : intervalL2 L U (increment E R) ≤ 2 * A * Real.sqrt R :=
    (hinc R ⟨hR.1, by linarith [hR.2]⟩).trans (by nlinarith [Real.sqrt_nonneg R])
  have hi2 : intervalL2 L U (increment E (2 * R)) ≤ 2 * A * Real.sqrt R :=
    (hinc (2 * R) ⟨by linarith [hR.1], by linarith [hR.2]⟩).trans (by nlinarith)
  obtain ⟨h1, h2, h3, h4, h5⟩ := fixed_scale_bounds hE hp hab hLa
    (by linarith [hR.2]) (by positivity : 0 ≤ 2 * A * Real.sqrt R) hi1 hi2
  have he1 : 2 * (2 * A * Real.sqrt R) / R = 4 * A / Real.sqrt R := by
    apply (div_eq_div_iff hp.ne' hs.ne').mpr
    nlinarith
  have he2 : (2 * A * Real.sqrt R) / Real.sqrt R = 2 * A :=
    mul_div_cancel_right₀ _ hs.ne'
  have he3 : (2 * A * Real.sqrt R) / R = 2 * A / Real.sqrt R := by
    apply (div_eq_div_iff hp.ne' hs.ne').mpr
    nlinarith
  have he4 : (2 * A * Real.sqrt R) / (R * Real.sqrt R) = 2 * A / R := by
    field_simp
  exact ⟨h1, he1 ▸ h2, fun x hx => he2 ▸ h3 x hx,
    he3 ▸ h4, fun x hx => he4 ▸ h5 x hx⟩

private lemma lbm_sub {f g : ℝ → ℝ} (hf : LocallyBoundedMeasurable f)
    (hg : LocallyBoundedMeasurable g) : LocallyBoundedMeasurable (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, fun a b => ?_⟩
  obtain ⟨M, hM, hb⟩ := hf.2 a b
  obtain ⟨N, hN, hc⟩ := hg.2 a b
  exact ⟨M + N, add_nonneg hM hN, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hb x hx) (hc x hx))⟩

private lemma single_residual_l2 {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {h a b K : ℝ} (hh : 0 < h) (hab : a ≤ b) (hK : 0 ≤ K)
    (hinc : ∀ u ∈ Icc (0 : ℝ) h, intervalL2 a b (increment E u) ≤ K) :
    intervalL2 a b (fun x => E x - windowAverage h E x) ≤ K := by
  have hprod := increment_sq_rectangle_integrable hE a b 0 h continuous_snd
  have hinner : IntervalIntegrable (fun x => ∫ t in (0 : ℝ)..h, increment E t x ^ 2)
      volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hh.le] using hprod.integral_prod_left
  have hpoint (x : ℝ) : (E x - windowAverage h E x) ^ 2 ≤
      (∫ t in (0 : ℝ)..h, increment E t x ^ 2) / h := by
    have hi : IntervalIntegrable (fun t => increment E t x) volume 0 h :=
      (increment_comp_integrableOn hE isCompact_uIcc
        continuous_id continuous_const).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => increment E t x ^ 2) volume 0 h := by
      simpa only [pow_two, id_eq] using
        (increment_product_comp_integrableOn hE isCompact_uIcc
          continuous_id continuous_const continuous_id continuous_const).intervalIntegrable
    have hcs := interval_cauchy_schwarz hh hi hi2
    have he : (∫ t in (0 : ℝ)..h, increment E t x) =
        h * (windowAverage h E x - E x) := by
      unfold increment windowAverage
      rw [intervalIntegral.integral_sub
        (by simpa using (locallyBoundedMeasurable_intervalIntegrable hE x (x + h)).comp_add_left x)
        intervalIntegrable_const, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      field_simp
    rw [he] at hcs
    apply (le_div_iff₀ hh).mpr
    nlinarith [mul_pos hh hh]
  have hle := intervalIntegral.integral_mono_on hab
    (square_integrable (lbm_sub hE (continuous_lbm (windowAverage_continuous hE hh))) a b)
    (hinner.div_const h) (fun x _ => hpoint x)
  rw [intervalIntegral.integral_div] at hle
  have hswap : (∫ x in a..b, ∫ t in (0 : ℝ)..h, increment E t x ^ 2) =
      ∫ t in (0 : ℝ)..h, ∫ x in a..b, increment E t x ^ 2 := by
    simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hh.le]
    exact integral_integral_swap hprod
  rw [hswap] at hle
  have hbnd : (∫ t in (0 : ℝ)..h, ∫ x in a..b, increment E t x ^ 2) ≤ h * K ^ 2 := by
    have hint : IntervalIntegrable (fun t => ∫ x in a..b, increment E t x ^ 2) volume 0 h := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
      simpa only [IntegrableOn, intervalIntegral.integral_of_le hab] using hprod.integral_prod_right
    have hc := intervalIntegral.integral_mono_on hh.le hint
      (intervalIntegrable_const (c := K ^ 2)) (fun t ht => ?_)
    · simpa using hc
    · have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hK).mpr (hinc t ht)
      simpa only [intervalL2, Real.sq_sqrt
        (intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
          (fun x => sq_nonneg _))] using hs
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hK, hle.trans ?_⟩
  exact (div_le_iff₀ hh).mpr (by nlinarith [hbnd])

/-- Uniform small-increment bounds control the residual after double averaging. -/
theorem smoothing_residual_intervalL2_le {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {h A a b L U : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hab : a ≤ b) (hLa : L ≤ a)
    (hmargin : b + 2 * h ≤ U)
    (hinc : ∀ u ∈ Icc (0 : ℝ) (2 * h),
      intervalL2 L U (increment E u) ≤ A * Real.sqrt h) :
    intervalL2 a b (fun x => E x - doubleAverage h E x) ≤ 2 * A * Real.sqrt h := by
  let q : ℝ → ℝ := fun x => E x - windowAverage h E x
  have hq : LocallyBoundedMeasurable q :=
    lbm_sub hE (continuous_lbm (windowAverage_continuous hE hh))
  have hqa : intervalL2 a b q ≤ A * Real.sqrt h :=
    single_residual_l2 hE hh hab (by positivity) (fun u hu =>
      (l2_mono (increment_lbm hE u) hLa hab (by linarith)).trans
        (hinc u ⟨hu.1, by linarith [hu.2]⟩))
  have hqb : intervalL2 a (b + h) q ≤ A * Real.sqrt h :=
    single_residual_l2 hE hh (by linarith) (by positivity) (fun u hu =>
      (l2_mono (increment_lbm hE u) hLa (by linarith) (by linarith)).trans
        (hinc u ⟨hu.1, by linarith [hu.2]⟩))
  have he : (fun x => E x - doubleAverage h E x) =
      fun x => q x + windowAverage h q x := by
    funext x
    have hi := (locallyBoundedMeasurable_intervalIntegrable hE x (x + h)).comp_add_left x
    have hc : IntervalIntegrable (fun r => windowAverage h E (x + r)) volume 0 h :=
      ((windowAverage_continuous hE hh).comp
        (continuous_const.add continuous_id)).intervalIntegrable 0 h
    have hqavg : windowAverage h q x = windowAverage h E x - doubleAverage h E x := by
      change (∫ r in (0 : ℝ)..h, E (x + r) - windowAverage h E (x + r)) / h = _
      rw [intervalIntegral.integral_sub (by simpa using hi) hc]
      change _ = (∫ r in (0 : ℝ)..h, E (x + r)) / h -
        (∫ r in (0 : ℝ)..h, windowAverage h E (x + r)) / h
      ring
    rw [hqavg]
    dsimp only [q]
    ring
  rw [he]
  have h := l2_linear hq (continuous_lbm (windowAverage_continuous hq hh)) hab 1 1
  simp only [one_mul, abs_one] at h
  exact h.trans (by nlinarith [(average_l2 hq hh hab).trans hqb])

/-- Uniform increment bounds give the residual and all five dyadic smoothing estimates.

The inner interval `[a,b]` and the working interval `[L,U]` are explicit so the same
estimate can be used with different enlargements. -/
theorem dyadic_smoothing_bounds_with_residual {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    {h k A B a b L U : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hab : a ≤ b) (hLa : L ≤ a)
    (hmargin : b + 4 * k ≤ U) (hmargin_residual : b + 2 * h ≤ U)
    (hinc : ∀ u ∈ Icc h (8 * k), intervalL2 L U (increment E u) ≤ A * Real.sqrt u)
    (hshort : ∀ u ∈ Icc (0 : ℝ) (2 * h),
      intervalL2 L U (increment E u) ≤ B * Real.sqrt h) :
    intervalL2 a b (fun x => E x - doubleAverage h E x) ≤ 2 * B * Real.sqrt h ∧
      ∀ R ∈ Icc h (2 * k),
        intervalL2 a b (smoothingBlock R E) ≤ 2 * A * Real.sqrt R ∧
        intervalL2 a b (deriv (smoothingBlock R E)) ≤ 4 * A / Real.sqrt R ∧
        (∀ x ∈ Icc a b, |smoothingBlock R E x| ≤ 2 * A) ∧
        intervalL2 a b (deriv (doubleAverage R E)) ≤ 2 * A / Real.sqrt R ∧
        (∀ x ∈ Icc a b, |deriv (doubleAverage R E) x| ≤ 2 * A / R) := by
  have hres := smoothing_residual_intervalL2_le hE hh hB hab hLa hmargin_residual hshort
  have hblocks := dyadic_smoothing_bounds hE hh hA hab hLa hmargin hinc
  exact ⟨hres, hblocks⟩

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingBounds
