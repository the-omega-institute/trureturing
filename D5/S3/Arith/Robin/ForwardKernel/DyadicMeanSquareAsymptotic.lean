/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The profile law gives kernel mean squares and strict positive-measure excursions. -/

import D5.S3.Arith.Robin.ForwardKernel.WeightRemoval
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthMeanSquare

/-! Price removal transfers the profile law and yields strict excursions of positive measure. -/

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareAsymptotic

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer ProfileKernelDefs
open WeightRemoval (unweightedResponse)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma point_weight_continuousOn {θ a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x : ℝ => x ^ (1 - θ) * Real.log x / x) (Icc a b) := by
  exact ((continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (ha.trans_le hx.1)))).mul
    (continuousOn_id.log (fun x hx => ne_of_gt (ha.trans_le hx.1)))).div
      continuousOn_id (fun x hx => ne_of_gt (ha.trans_le hx.1))

private lemma point_weight_scaled (θ : ℝ) {X : ℝ} (hX : 1 < X) :
    (∫ x in X..(2 * X), x ^ (1 - θ) * Real.log x / x) / meanSquareScale θ X =
      (∫ v in (1 : ℝ)..2, v ^ (-θ)) +
        (∫ v in (1 : ℝ)..2, v ^ (-θ) * Real.log v) / Real.log X := by
  have hX0 : 0 < X := by linarith
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hp : X ^ (1 - θ) ≠ 0 := (Real.rpow_pos_of_pos hX0 _).ne'
  have hv : ContinuousOn (fun v : ℝ => v ^ (-θ)) (Icc (1 : ℝ) 2) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (by change x ≠ 0; linarith [hx.1]))
  have hvl : ContinuousOn (fun v : ℝ => v ^ (-θ) * Real.log v)
      (Icc (1 : ℝ) 2) := hv.mul (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun x : ℝ => x ^ (1 - θ) * Real.log x / x) (a := 1) (b := 2) X
  simp only [smul_eq_mul, mul_one, mul_comm X 2] at hs
  rw [← hs]
  have he : (∫ v in (1 : ℝ)..2, (X * v) ^ (1 - θ) * Real.log (X * v) / (X * v)) =
      X ^ (1 - θ) / X *
        (Real.log X * (∫ v in (1 : ℝ)..2, v ^ (-θ)) +
          ∫ v in (1 : ℝ)..2, v ^ (-θ) * Real.log v) := by
    calc
      _ = ∫ v in (1 : ℝ)..2, X ^ (1 - θ) / X *
          (Real.log X * v ^ (-θ) + v ^ (-θ) * Real.log v) := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hv0 : 0 < v := by rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hv; linarith [hv.1]
        dsimp only
        rw [Real.mul_rpow hX0.le hv0.le, Real.log_mul hX0.ne' hv0.ne']
        have hpow : v ^ (-θ) = v ^ (1 - θ) / v := by
          rw [← Real.rpow_sub_one hv0.ne']; congr 1 <;> ring
        rw [hpow]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add ((hv.intervalIntegrable_of_Icc (by norm_num)).const_mul _)
            (hvl.intervalIntegrable_of_Icc (by norm_num)),
          intervalIntegral.integral_const_mul]
  rw [he]
  unfold meanSquareScale
  field_simp [hX0.ne', hp, hlog]

/-- The dyadic point weight has the explicit integral limit for every exponent in `(0,1)`. -/
theorem dyadic_point_weight_integral_tendsto {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Tendsto
      (fun X => (∫ x in X..(2 * X), x ^ (1 - θ) * Real.log x / x) / meanSquareScale θ X)
      atTop (𝓝 (((2 : ℝ) ^ (1 - θ) - 1) / (1 - θ))) := by
  have hi : (∫ v in (1 : ℝ)..2, v ^ (-θ)) =
      ((2 : ℝ) ^ (1 - θ) - 1) / (1 - θ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -θ))]
    rw [show -θ + 1 = 1 - θ by ring, Real.one_rpow]
  have hz : Tendsto (fun X : ℝ =>
      (∫ v in (1 : ℝ)..2, v ^ (-θ) * Real.log v) / Real.log X)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hh := (tendsto_const_nhds (x := ((2 : ℝ) ^ (1 - θ) - 1) / (1 - θ))).add hz
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  rw [point_weight_scaled θ hX, hi]

private lemma normalized_square {x y : ℝ} (hx : 0 ≤ x) :
    (y / Real.sqrt x) ^ 2 = y ^ 2 / x := by
  rw [div_pow, Real.sq_sqrt hx]

/-- The sole variance-band hypothesis implies the full profile-kernel dyadic mean-square law. -/
theorem profile_kernel_dyadic_mean_square_asymptotic
    {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {g : ℝ → ℝ} (hg : ProfileIntegrable g) :
    Tendsto
      (fun X => (∫ x in X..(2 * X), profileResponse E θ g x ^ 2 / x) /
        meanSquareScale θ X)
      atTop (𝓝 (Q g * ((2 : ℝ) ^ (1 - θ) - 1))) := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hL : 0 ≤ Q g * ((2 : ℝ) ^ (1 - θ) - 1) := by
    have hQ : 0 ≤ Q g := by
      rw [ProfileQuadraticForm.Q_eq_tail_energy hg]
      exact intervalIntegral.integral_nonneg_of_forall zero_le_one fun _ => sq_nonneg _
    exact mul_nonneg hQ (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) (by linarith)))
  have he (x : ℝ) (hx : 0 < x) :
      unweightedResponse E θ g x / Real.sqrt x = movingAverage E θ g x := by
    unfold unweightedResponse
    exact mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hx).ne'
  have hgLimit : Tendsto (fun X => (∫ x in X..(2 * X),
      (unweightedResponse E θ g x / Real.sqrt x) ^ 2) / meanSquareScale θ X)
      atTop (𝓝 (Q g * ((2 : ℝ) ^ (1 - θ) - 1))) := by
    apply (MovingLengthMeanSquare.moving_profile_mean_square_tendsto hE hB hV hg).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
    dsimp only
    rw [he x (hX.trans_le hx.1)]
  have hgmem : ∀ᶠ X : ℝ in atTop,
      MemLp (fun x => unweightedResponse E θ g x / Real.sqrt x) 2
        (volume.restrict (Ioc X (2 * X))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hm := MovingLengthRegularity.profileAverage_variable_memLp hE hg
      (measurable_id.pow_const θ) (by linarith : X ≤ 2 * X) (Real.rpow_pos_of_pos hX θ)
      (L := (2 * X) ^ θ) (fun x hx =>
        ⟨Real.rpow_le_rpow hX.le hx.1 hθ0.le,
          Real.rpow_le_rpow (hX.trans_le hx.1).le hx.2 hθ0.le⟩)
    refine MemLp.ae_eq ?_ hm
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (he x (hX.trans hx.1)).symm
  have hdLimit : Tendsto (fun X => (∫ x in X..(2 * X),
      (profileResponse E θ g x / Real.sqrt x -
        unweightedResponse E θ g x / Real.sqrt x) ^ 2) / meanSquareScale θ X)
      atTop (𝓝 0) := by
    apply (WeightRemoval.profile_weight_removal_l2 hE hB hV hg).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
    dsimp only
    rw [← sub_div, normalized_square (hX.le.trans hx.1)]
  have hh := TriangularMeanSquare.interval_square_tendsto_of_l2_negligible hL
    (show ∀ᶠ X : ℝ in atTop, X ≤ 2 * X by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      linarith)
    (show ∀ᶠ X : ℝ in atTop, 0 < meanSquareScale θ X by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
      exact mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < X) _) (Real.log_pos hX))
    (show ∀ᶠ X : ℝ in atTop, MemLp (fun x => profileResponse E θ g x / Real.sqrt x) 2
        (volume.restrict (Ioc X (2 * X))) by
      filter_upwards [eventually_ge_atTop (3 : ℝ)] with X hX
      exact WeightRemoval.profileResponse_normalized_memLp hE hg θ hX (by linarith))
    hgmem hgLimit hdLimit
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
  exact normalized_square (hX.le.trans hx.1)

/-- Every sufficiently large dyadic interval has a positive-measure set of strict excursions. -/
theorem profile_kernel_dyadic_large_set
    {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {g : ℝ → ℝ} (hg : ProfileIntegrable g)
    (hg_ne : ¬ (g =ᵐ[unitMeasure] 0))
    {c : ℝ} (hc0 : 0 < c) (hc : c < Real.sqrt ((1 - θ) * Q g)) :
    ∀ᶠ X : ℝ in atTop,
      0 < volume {x : ℝ | x ∈ Icc X (2 * X) ∧
        c * x ^ ((1 - θ) / 2) * Real.sqrt (Real.log x) < |profileResponse E θ g x|} := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hQ := (ProfileQuadraticForm.Q_pos_iff hg).mpr hg_ne
  have hMS := profile_kernel_dyadic_mean_square_asymptotic hE hB hV hg
  have hcSq : c ^ 2 < (1 - θ) * Q g := by
    have hh := (sq_lt_sq₀ hc0.le (Real.sqrt_nonneg _)).mpr hc
    rwa [Real.sq_sqrt (by positivity : 0 ≤ (1 - θ) * Q g)] at hh
  have hp : 0 < (2 : ℝ) ^ (1 - θ) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by linarith))
  have hC : 0 < Q g * ((2 : ℝ) ^ (1 - θ) - 1) := mul_pos hQ hp
  have hgap : 0 < Q g * ((2 : ℝ) ^ (1 - θ) - 1) -
      c ^ 2 * (((2 : ℝ) ^ (1 - θ) - 1) / (1 - θ)) := by
    have hh := mul_pos (sub_pos.mpr hcSq) hp
    apply (div_pos hh (sub_pos.mpr hθ1)).trans_eq
    field_simp
  have hd := hMS.sub ((dyadic_point_weight_integral_tendsto hθ0 hθ1).const_mul (c ^ 2))
  filter_upwards [hd.eventually (eventually_gt_nhds hgap),
    hMS.eventually (eventually_gt_nhds hC), eventually_gt_atTop (1 : ℝ)]
    with X hgapX hMSX hX
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hS : 0 < meanSquareScale θ X :=
    mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)
  by_contra hn
  have hz : volume {x : ℝ | x ∈ Icc X (2 * X) ∧
      c * x ^ ((1 - θ) / 2) * Real.sqrt (Real.log x) < |profileResponse E θ g x|} = 0 :=
    le_antisymm (not_lt.mp hn) bot_le
  have hne : (∫ x in X..(2 * X), profileResponse E θ g x ^ 2 / x) ≠ 0 := by
    intro hz
    rw [hz, zero_div] at hMSX
    exact (lt_irrefl _ hMSX)
  have hi := intervalIntegral.intervalIntegrable_of_integral_ne_zero hne
  have hw : IntervalIntegrable (fun x : ℝ => x ^ (1 - θ) * Real.log x / x)
      volume X (2 * X) :=
    (point_weight_continuousOn hX0).intervalIntegrable_of_Icc hXX
  have hbound : (fun x : ℝ => profileResponse E θ g x ^ 2 / x) ≤ᵐ[volume.restrict (Icc X (2 * X))]
      (fun x => c ^ 2 * (x ^ (1 - θ) * Real.log x / x)) := by
    have hnot := (measure_eq_zero_iff_ae_notMem.mp hz).filter_mono
      (ae_mono (Measure.restrict_le_self : volume.restrict (Icc X (2 * X)) ≤ volume))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hnot] with x hx hnot
    have hx0 : 0 < x := hX0.trans_le hx.1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hx.1])
    have hnonneg : 0 ≤ c * x ^ ((1 - θ) / 2) * Real.sqrt (Real.log x) := by positivity
    have hle : |profileResponse E θ g x| ≤ c * x ^ ((1 - θ) / 2) * Real.sqrt (Real.log x) :=
      le_of_not_gt (fun hlt => hnot ⟨hx, hlt⟩)
    have hs := (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr hle
    rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hlog] at hs
    have he : (x ^ ((1 - θ) / 2)) ^ 2 = x ^ (1 - θ) := by
      rw [← Real.rpow_mul_natCast hx0.le]
      congr 1
      ring
    rw [he] at hs
    calc
      _ ≤ (c ^ 2 * x ^ (1 - θ) * Real.log x) / x :=
        div_le_div_of_nonneg_right hs hx0.le
      _ = _ := by ring
  have hb := intervalIntegral.integral_mono_ae_restrict hXX hi (hw.const_mul (c ^ 2)) hbound
  rw [intervalIntegral.integral_const_mul] at hb
  have hb' := div_le_div_of_nonneg_right hb hS.le
  rw [mul_div_assoc] at hb'
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicMeanSquareAsymptotic
