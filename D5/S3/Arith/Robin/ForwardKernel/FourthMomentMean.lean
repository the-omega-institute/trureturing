/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentMean
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Short averaging makes the first profile moment negligible at its variance scale. -/

import D5.S3.Arith.Robin.ForwardKernel.FourScaleCovariance
import D5.S3.Arith.Robin.ForwardKernel.ProfileCrossIntegral

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentMean

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer ProfileKernelDefs CrossExponentDefs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma primitive_le_of_average {E : ℝ → ℝ} {θ s X M U F : ℝ}
    (hE : LocallyBoundedMeasurable E) (hθ : 0 < θ)
    (hX : 0 < X) (hM : 0 < M) (hMX : M ≤ X)
    (hF : 0 ≤ F) (hU : 0 ≤ U)
    (hf : intervalL2 X (3 * X) (movingIncrement E θ s) ≤ F)
    (ha : intervalL2 X (2 * X) (windowAverage M (movingIncrement E θ s)) ≤ U)
    {y : ℝ} (hy : y ∈ Icc X (2 * X)) :
    |∫ x in X..y, movingIncrement E θ s x| ≤
      U * Real.sqrt X + 2 * F * Real.sqrt M := by
  let f := movingIncrement E θ s
  have hi (a b : ℝ) := FourScaleCovariance.moving_memLp hE hθ a b (s := s)
  have norm_mono {a b : ℝ} (ha : X ≤ a) (hab : a ≤ b) (hb : b ≤ 3 * X) :
      intervalL2 a b f ≤ F := by
    apply le_trans (Real.sqrt_le_sqrt ?_) hf
    exact intervalIntegral.integral_mono_interval ha hab hb
      (Eventually.of_forall (fun _ => sq_nonneg _))
      (TranslationStripBounds.moving_sq_integrable hE hθ X (3 * X))
  have havg : MemLp (windowAverage M f) 2 (volume.restrict (Ioc X y)) :=
    FourScaleCovariance.average_memLp hE hθ
  have han : intervalL2 X y (windowAverage M f) ≤ U := by
    apply le_trans (Real.sqrt_le_sqrt ?_) ha
    exact intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
      (Eventually.of_forall (fun _ => sq_nonneg _))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X ≤ 2 * X)).mpr
        ((memLp_two_iff_integrable_sq
          (FourScaleCovariance.average_memLp hE hθ).aestronglyMeasurable).mp
            (FourScaleCovariance.average_memLp hE hθ (s := s) (M := M))))
  have hconst {a b : ℝ} (hab : a ≤ b) :
      intervalL2 a b (fun _ => (1 : ℝ)) = Real.sqrt (b - a) := by
    simp [intervalL2, intervalIntegral.integral_const]
  have hprod : Integrable (fun p : ℝ × ℝ => f (p.1 + p.2) * (1 : ℝ))
      ((volume.restrict (Ioc X y)).prod (volume.restrict (Ioc (0 : ℝ) M))) := by
    rw [Measure.prod_restrict]
    have hp := increment_comp_integrableOn (μ := volume.prod volume)
      (K := Icc X y ×ˢ Icc (0 : ℝ) M) hE (isCompact_Icc.prod isCompact_Icc)
      ((continuous_const (y := s)).mul ((Real.continuous_rpow_const hθ.le).comp
        (continuous_fst.add continuous_snd))) (continuous_fst.add continuous_snd)
    simpa only [mul_one, f, movingIncrement, IntegrableOn, Pi.add_apply, Pi.mul_apply, Function.comp_apply] using
      hp.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have h := FourScaleCovariance.covariance_of_norm_bounds
    (f := f) (z := fun _ => (1 : ℝ)) (M := M) (F := F)
    (Z := Real.sqrt X) (U := U) (D := 0) (S := Real.sqrt M)
    hy.1 hM hF hU hi (fun _ _ => memLp_const 1) havg hprod
    (by
      intro v hv
      exact norm_mono (by linarith [hv.1]) (by linarith [hy.1])
        (by linarith [hy.2, hv.2]))
    (by rw [hconst hy.1]; exact Real.sqrt_le_sqrt (by linarith [hy.2])) han
    (by intro v hv; simp [intervalL2])
    (by
      intro v hv e he
      simp only [mem_insert_iff, mem_singleton_iff] at he
      have heX : X ≤ e := by rcases he with rfl | rfl <;> linarith [hy.1]
      have he2X : e ≤ 2 * X := by rcases he with rfl | rfl <;> linarith [hy.2]
      exact ⟨norm_mono heX (by linarith [hv.1]) (by linarith [hv.2]),
        by rw [hconst (by linarith [hv.1])]; exact Real.sqrt_le_sqrt (by linarith [hv.2])⟩)
  simpa only [mul_one, mul_zero, add_zero] using h

private lemma moving_primitive_bound {E : ℝ → ℝ} {α θ β ν : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hθν : θ < ν) (hνβ : ν < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc X (2 * X),
      |∫ x in X..y, movingIncrement E θ s x| ≤
        C * Real.sqrt (Real.log X) *
          (X ^ (1 + θ - ν / 2) + X ^ ((1 + θ + ν) / 2)) := by
  have hθ : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hν1 : ν < 1 := hνβ.trans hB.2.2.2
  have hBν : ValidBand α ν β := ⟨hB.1, hB.2.1.trans hθν, hνβ, hB.2.2.2⟩
  have hM := TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBν hV
  have hk := TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hB hV
  have hhM : Asymptotics.IsBigO atTop (fun X : ℝ => X ^ θ) (fun X => X ^ ν) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith : 0 < X) _),
      one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hX hθν.le
  have hMX : Asymptotics.IsLittleO atTop (fun X : ℝ => X ^ ν) (fun X => X) := by
    apply Asymptotics.isLittleO_of_tendsto'
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX hz; exact (hX.ne' hz).elim)
    apply (tendsto_rpow_neg_atTop (sub_pos.mpr hν1)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [show -(1 - ν) = ν - 1 by ring, Real.rpow_sub hX, Real.rpow_one]
  obtain ⟨Ca, hCa, hav⟩ := MovingShortAverage.averaged_moving_increment_l2_bound
    hE hθ hθ1 (A := 1) (B := 2) zero_lt_one (by norm_num) hM hhM hMX
  obtain ⟨Cf, hCf, hfv⟩ := TranslationStripBounds.moving_square_bound_of_comparable
    hE hθ hθ1 (A := 1) (B := 3) zero_lt_one (by norm_num) hk
  refine ⟨Ca + 2 * Real.sqrt Cf, by positivity, ?_⟩
  filter_upwards [hav, hfv, eventually_ge_atTop (1 : ℝ)] with X hav hfv hX
  simp only [one_mul] at hav hfv
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpow (a : ℝ) : Real.sqrt (X ^ a) = X ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have hterm₁ : (X ^ θ / X ^ ν) * Real.sqrt (X * Real.log X) *
      Real.sqrt (X ^ ν) * Real.sqrt X =
      Real.sqrt (Real.log X) * X ^ (1 + θ - ν / 2) := by
    rw [Real.sqrt_mul hX0.le, hpow, Real.sqrt_eq_rpow, ← Real.rpow_sub hX0]
    calc
      _ = Real.sqrt (Real.log X) *
          (X ^ (θ - ν) * X ^ (1 / 2 : ℝ) * X ^ (ν / 2) * X ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
        congr 2
        ring
  have hterm₂ : Real.sqrt (X * Real.log X) * Real.sqrt (X ^ θ) *
      Real.sqrt (X ^ ν) = Real.sqrt (Real.log X) * X ^ ((1 + θ + ν) / 2) := by
    rw [Real.sqrt_mul hX0.le, hpow, hpow, Real.sqrt_eq_rpow]
    calc
      _ = Real.sqrt (Real.log X) *
          (X ^ (1 / 2 : ℝ) * X ^ (θ / 2) * X ^ (ν / 2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
        congr 2
        ring
  intro s hs y hy
  have hf : intervalL2 X (3 * X) (movingIncrement E θ s) ≤
      Real.sqrt Cf * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ θ) := by
    apply (Real.sqrt_le_sqrt (hfv s hs)).trans_eq
    rw [show Cf * X * X ^ θ * Real.log X = Cf * (X * Real.log X) * X ^ θ by ring,
      Real.sqrt_mul (by positivity : 0 ≤ Cf * (X * Real.log X)), Real.sqrt_mul hCf.le]
  have hp := primitive_le_of_average hE hθ hX0 (Real.rpow_pos_of_pos hX0 ν)
    (Real.rpow_le_self_of_one_le hX hν1.le) (by positivity) (by positivity)
    hf (hav s hs) hy
  calc
    _ ≤ (Ca * (X ^ θ / X ^ ν) * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ ν)) *
        Real.sqrt X + 2 * (Real.sqrt Cf * Real.sqrt (X * Real.log X) *
        Real.sqrt (X ^ θ)) * Real.sqrt (X ^ ν) := hp
    _ = Ca * (Real.sqrt (Real.log X) * X ^ (1 + θ - ν / 2)) +
        2 * Real.sqrt Cf * (Real.sqrt (Real.log X) * X ^ ((1 + θ + ν) / 2)) := by
      rw [← hterm₁, ← hterm₂]
      ring
    _ ≤ _ := by
      nlinarith [mul_nonneg (mul_nonneg hCa.le (Real.sqrt_nonneg (Real.log X)))
        (Real.rpow_nonneg hX0.le ((1 + θ + ν) / 2)),
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg Cf) (Real.sqrt_nonneg (Real.log X)))
        (Real.rpow_nonneg hX0.le (1 + θ - ν / 2))]

private lemma weighted_moving_mean_bound {E : ℝ → ℝ} {α θ β ν : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hθν : θ < ν) (hνβ : ν < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
      |∫ x in X..(2 * X), ProfileCrossIntegral.crossWeight θ (1 / 2) s 0 x *
          movingIncrement E θ s x| ≤
        C * Real.sqrt (Real.log X) *
          (X ^ ((1 - ν) / 2) + X ^ ((ν - θ) / 2)) := by
  have hθ : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨C, hC, hp⟩ := moving_primitive_bound hE hB hV hθν hνβ
  refine ⟨C * (27 + θ + 1 / 2), by positivity, ?_⟩
  filter_upwards [hp, eventually_ge_atTop (4 : ℝ)] with X hp hX
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  intro s hs
  have hi : IntervalIntegrable (movingIncrement E θ s) volume X (2 * X) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hXX).mpr
      ((FourScaleCovariance.moving_memLp hE hθ X (2 * X)).integrable (by norm_num))
  have hb := WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound
    hXX hi (ProfileCrossIntegral.crossWeight_contDiffOn (a := θ) (b := 1 / 2) hX hs.1 (by norm_num : (0 : ℝ) ≤ 0))
    (show 0 ≤ C * Real.sqrt (Real.log X) *
      (X ^ (1 + θ - ν / 2) + X ^ ((1 + θ + ν) / 2)) by positivity)
    (hp s hs)
  have hv := ProfileCrossIntegral.crossWeight_variation hθ hθ1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hX hs
      (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  apply (hb.trans (mul_le_mul_of_nonneg_left hv (by positivity))).trans_eq
  have he₁ : X ^ (1 + θ - ν / 2) * X ^ (-θ - 1 / 2) = X ^ ((1 - ν) / 2) := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  have he₂ : X ^ ((1 + θ + ν) / 2) * X ^ (-θ - 1 / 2) = X ^ ((ν - θ) / 2) := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  calc
    _ = C * (27 + θ + 1 / 2) * Real.sqrt (Real.log X) *
        (X ^ (1 + θ - ν / 2) * X ^ (-θ - 1 / 2) +
          X ^ ((1 + θ + ν) / 2) * X ^ (-θ - 1 / 2)) := by ring
    _ = _ := by rw [he₁, he₂]

private lemma crossWeight_zero {θ s x : ℝ} (hx : 3 ≤ x) :
    ProfileCrossIntegral.crossWeight θ (1 / 2) s 0 x =
      x ^ (-θ - 1 / 2) * priceRatio x (s * x ^ θ) := by
  have hw := (OriginalMovingWindowMoment.weight_pos (by linarith : 1 < x)).ne'
  simp [ProfileCrossIntegral.crossWeight, priceRatio, hw]

private lemma profile_mean_eq {E g : ℝ → ℝ} {θ X : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hX : 4 ≤ X) :
    (∫ x in X..(2 * X), profileResponse E θ g x / x) =
      ∫ s, g s * (∫ x in X..(2 * X),
        ProfileCrossIntegral.crossWeight θ (1 / 2) s 0 x * movingIncrement E θ s x)
        ∂unitMeasure := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  let μ := volume.restrict (Ioc X (2 * X))
  let k : ℝ × ℝ → ℝ := fun p =>
    p.1 ^ (-θ - 1 / 2) * priceRatio p.1 (p.2 * p.1 ^ θ) *
      increment E (p.2 * p.1 ^ θ) p.1
  have hk : Measurable k :=
    ((measurable_fst.pow_const _).mul
      (WeightRemoval.price_measurable.comp
        (measurable_fst.prodMk (measurable_snd.mul (measurable_fst.pow_const θ))))).mul
          (WeightRemoval.increment_measurable hE θ)
  obtain ⟨M, hM, hMb⟩ := WeightRemoval.local_increment_bound hE θ hX0 hXX
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-θ - 1 / 2)) (Icc X (2 * X)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hX0.trans_le hx.1)))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hprod : Integrable (fun p : ℝ × ℝ => g p.2 * k p) (μ.prod unitMeasure) := by
    have hgprod : Integrable (fun p : ℝ × ℝ => g p.2) (μ.prod unitMeasure) := by
      simpa only [one_mul] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ).mul_prod hg.2
    apply hgprod.mul_bdd hk.aestronglyMeasurable (c := |K| * M)
    have hrect : ∀ᵐ p ∂(μ.prod unitMeasure),
        p.1 ∈ Ioc X (2 * X) ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
      dsimp [μ, unitMeasure]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hrect] with p hp
    have hx : p.1 ∈ Icc X (2 * X) := ⟨hp.1.1.le, hp.1.2⟩
    have hs : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp.2.1.le, hp.2.2⟩
    obtain ⟨hr0, hr1⟩ := WeightControl.price_bounds (x := p.1) (u := p.2 * p.1 ^ θ) (by linarith [hx.1])
      (mul_nonneg hs.1 (Real.rpow_nonneg (hX0.trans_le hx.1).le _))
    simp only [k, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul
      ((mul_le_of_le_one_right (abs_nonneg _) hr1).trans ((hK _ hx).trans (le_abs_self K)))
      (hMb _ hx _ hs) (abs_nonneg _) (by positivity)
  have hx_eq (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      profileResponse E θ g x / x = ∫ s, g s * k (x, s) ∂unitMeasure := by
    have hx0 := hX0.trans_le hx.1
    have hsqrt := Real.sq_sqrt hx0.le
    have hpower : Real.sqrt x / x / x ^ θ = x ^ (-θ - 1 / 2) := by
      rw [Real.sqrt_eq_rpow]
      calc
        _ = x ^ ((1 / 2 : ℝ) - 1 - θ) := by
          rw [Real.rpow_sub hx0, Real.rpow_sub hx0, Real.rpow_one]
        _ = _ := by congr 1; ring
    have he := WeightRemoval.normalized_eq (E := E) (g := g) (θ := θ) hx0
    have hn : profileResponse E θ g x = Real.sqrt x / x ^ θ *
        ∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ) ∂unitMeasure := by
      apply (div_eq_iff (Real.sqrt_pos.mpr hx0).ne').mp at he
      rw [he]
      ring
    rw [hn]
    calc
      _ = (Real.sqrt x / x / x ^ θ) *
          ∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ) ∂unitMeasure := by ring
      _ = _ := by
        rw [hpower, ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun s => by dsimp [k]; ring)
  have heq : (∫ x in X..(2 * X), profileResponse E θ g x / x) =
      ∫ x in X..(2 * X), ∫ s, g s * k (x, s) ∂unitMeasure := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hx_eq x (by simpa only [uIcc_of_le hXX] using hx)
  rw [heq, intervalIntegral.integral_of_le hXX]
  change (∫ x, ∫ s, g s * k (x, s) ∂unitMeasure ∂μ) = _
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [intervalIntegral.integral_of_le hXX, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change g s * k (x, s) = g s *
    (ProfileCrossIntegral.crossWeight θ (1 / 2) s 0 x * movingIncrement E θ s x)
  rw [crossWeight_zero (θ := θ) (s := s) (by linarith [hx.1] : 3 ≤ x)]
  rfl

/-- The first profile moment is bounded uniformly by the two separated power scales. -/
theorem profile_response_mean_bound
    {E : ℝ → ℝ} {α θ β ν : ℝ} {g : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hθν : θ < ν) (hνβ : ν < β)
    (hg : ProfileIntegrable g) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        |∫ x in X..(2 * X), profileResponse E θ g x / x| ≤
          C * profileL1 g * Real.sqrt (Real.log X) *
            (X ^ ((1 - ν) / 2) + X ^ ((ν - θ) / 2)) := by
  obtain ⟨C, hC, hb⟩ := weighted_moving_mean_bound hE hB hV hθν hνβ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4 : ℝ)] with X hb hX
  rw [profile_mean_eq hE hg hX]
  have hn := norm_integral_le_of_norm_le
    (hg.2.abs.mul_const (C * Real.sqrt (Real.log X) *
      (X ^ ((1 - ν) / 2) + X ^ ((ν - θ) / 2)))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hb s ⟨hs.1.le, hs.2⟩) (abs_nonneg _))
  simpa only [Real.norm_eq_abs, integral_mul_const, profileL1, mul_assoc, mul_left_comm C]
    using hn

/-- The first profile moment divided by the square root of its variance scale tends to zero. -/
theorem profile_response_mean_tendsto_zero
    {E : ℝ → ℝ} {α θ β ν : ℝ} {g : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hθν : θ < ν) (hνβ : ν < β)
    (hg : ProfileIntegrable g) :
    Tendsto
      (fun X => (∫ x in X..(2 * X), profileResponse E θ g x / x) /
        Real.sqrt (meanSquareScale θ X))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := profile_response_mean_bound hE hB hV hθν hνβ hg
  have hν1 : ν < 1 := hνβ.trans hB.2.2.2
  have hd₁ := tendsto_rpow_neg_atTop (by linarith : 0 < (ν - θ) / 2)
  have hd₂ := tendsto_rpow_neg_atTop (by linarith : 0 < (1 - ν) / 2)
  have hd : Tendsto (fun X : ℝ => C * profileL1 g *
      (X ^ (-((ν - θ) / 2)) + X ^ (-((1 - ν) / 2)))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hd₁.add hd₂).const_mul (C * profileL1 g)
  apply squeeze_zero_norm' ?_ hd
  filter_upwards [hb, eventually_ge_atTop (4 : ℝ)] with X hb hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hslog : 0 < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr hlog
  have hspow : 0 < X ^ ((1 - θ) / 2) := Real.rpow_pos_of_pos hX0 _
  have he : Real.sqrt (meanSquareScale θ X) =
      X ^ ((1 - θ) / 2) * Real.sqrt (Real.log X) := by
    rw [meanSquareScale, Real.sqrt_mul (Real.rpow_nonneg hX0.le _),
      Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    congr 2
    ring
  have he₁ : X ^ ((1 - ν) / 2) / X ^ ((1 - θ) / 2) = X ^ (-((ν - θ) / 2)) := by
    rw [← Real.rpow_sub hX0]
    congr 1
    ring
  have he₂ : X ^ ((ν - θ) / 2) / X ^ ((1 - θ) / 2) = X ^ (-((1 - ν) / 2)) := by
    rw [← Real.rpow_sub hX0]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_div, he, abs_of_pos (mul_pos hspow hslog)]
  apply (div_le_div_of_nonneg_right hb (mul_pos hspow hslog).le).trans_eq
  calc
    _ = C * profileL1 g * (X ^ ((1 - ν) / 2) / X ^ ((1 - θ) / 2) +
        X ^ ((ν - θ) / 2) / X ^ ((1 - θ) / 2)) := by
      field_simp
    _ = _ := by rw [he₁, he₂]

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentMean
