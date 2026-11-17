/- GID: D5/S3/Arith/Robin/ForwardKernel/CommonBandCovariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CommonBandCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common variance band bounds covariances of dyadic smoothing blocks uniformly in scale. -/

import D5.S3.Arith.Robin.ForwardKernel.DyadicCovariancePairs
import D5.S3.Arith.Robin.ForwardKernel.TranslationStripBounds

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandCovariance

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs VarianceTransfer CrossExponentDefs
open AveragingRegularity DyadicCovariancePairs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem outer_smoothing_bounds
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      intervalL2 (X / 4) (8 * X) (fun x => E x - doubleAverage (X ^ a) E x) ≤
        C * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ a) ∧
      ∀ R ∈ Icc (X ^ a) (2 * X ^ b),
        intervalL2 (X / 4) (8 * X) (smoothingBlock R E) ≤
          C * Real.sqrt (X * Real.log X) * Real.sqrt R ∧
        intervalL2 (X / 4) (8 * X) (deriv (smoothingBlock R E)) ≤
          C * Real.sqrt (X * Real.log X) / Real.sqrt R ∧
        (∀ x ∈ Icc (X / 4) (8 * X),
          |smoothingBlock R E x| ≤ C * Real.sqrt (X * Real.log X)) ∧
        intervalL2 (X / 4) (8 * X) (deriv (doubleAverage R E)) ≤
          C * Real.sqrt (X * Real.log X) / Real.sqrt R ∧
        (∀ x ∈ Icc (X / 4) (8 * X),
          |deriv (doubleAverage R E) x| ≤ C * Real.sqrt (X * Real.log X) / R) := by
  obtain ⟨D, hD, hvar⟩ := MovingLengthVariance.band_range_variance_bound
    hE hBa hab hbβ (d := 20) (by norm_num) hV
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  refine ⟨64 * Real.sqrt D, by positivity, ?_⟩
  filter_upwards [hvar, eventually_ge_atTop (8 : ℝ)] with X hvar hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  have hk : 0 < X ^ b := Real.rpow_pos_of_pos hX0 b
  have hhk : X ^ a ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le (by linarith) hab.le
  have hkX : X ^ b ≤ X := Real.rpow_le_self_of_one_le (by linarith) hb1.le
  let A := 8 * Real.sqrt D * Real.sqrt (X * Real.log X)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hi (u : ℝ) : IntervalIntegrable (fun x => increment E u x ^ 2) volume 1 (20 * X) := by
    simpa only [pow_two, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hinc : ∀ u ∈ Icc (X ^ a) (8 * X ^ b),
      intervalL2 (X / 8) (16 * X) (increment E u) ≤ A * Real.sqrt u := by
    intro u hu
    have hm := intervalIntegral.integral_mono_interval (show (1 : ℝ) ≤ X / 8 by linarith)
      (show X / 8 ≤ 16 * X by linarith) (show 16 * X ≤ 20 * X by linarith)
      (Eventually.of_forall fun x => sq_nonneg (increment E u x)) (hi u)
    have hs := Real.sqrt_le_sqrt (hm.trans (hvar u hu))
    have he : Real.sqrt (D * X * u * Real.log X) =
        Real.sqrt D * Real.sqrt (X * Real.log X) * Real.sqrt u := by
      rw [show D * X * u * Real.log X = D * (X * Real.log X) * u by ring,
        Real.sqrt_mul (by positivity : 0 ≤ D * (X * Real.log X)), Real.sqrt_mul hD.le]
    change Real.sqrt _ ≤ _
    rw [he] at hs
    apply hs.trans
    dsimp [A]
    nlinarith only [show 0 ≤ Real.sqrt D * Real.sqrt (X * Real.log X) * Real.sqrt u by positivity]
  have hshort : ∀ u ∈ Icc (0 : ℝ) (2 * X ^ a),
      intervalL2 (X / 8) (16 * X) (increment E u) ≤ A * Real.sqrt (X ^ a) := by
    intro u hu
    have hc := MovingEndpointVariance.two_endpoint_increment_square_le
      (p := fun x : ℝ => x) (q := fun x => x + u)
      (p' := fun _ => 1) (q' := fun _ => 1)
      (R := X ^ a) (Y := 20 * X) (C₀ := 2) (m := 1)
      (K := 4 * D * X * X ^ a * Real.log X)
      hE (show X / 8 ≤ 16 * X by linarith) hh (by norm_num) zero_lt_one (by positivity)
      continuous_id.continuousOn (continuous_id.add_const u).continuousOn
      (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
      (fun x _ => ((hasDerivAt_id x).add_const u).hasDerivWithinAt)
      (fun _ _ => le_rfl) (fun _ _ => le_rfl)
      (by
        intro x hx
        exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
          ⟨by linarith [hx.1, hu.1], by linarith [hx.2, hu.2]⟩⟩)
      (by intro x _; simpa only [add_sub_cancel_left] using hu)
      (by
        intro v hv
        have hb := hvar v ⟨hv.1, by linarith [hv.2]⟩
        apply hb.trans
        have hv' : v ≤ 4 * X ^ a := by linarith [hv.2]
        nlinarith only [mul_le_mul_of_nonneg_left hv'
          (show 0 ≤ D * X * Real.log X by positivity)])
    have hs := Real.sqrt_le_sqrt hc
    have he : Real.sqrt ((2 * (2 + 2) / (1 : ℝ)) * (4 * D * X * X ^ a * Real.log X)) ≤
        A * Real.sqrt (X ^ a) := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity, ?_⟩
      dsimp [A]
      simp only [mul_pow, Real.sq_sqrt hD.le,
        Real.sq_sqrt (mul_nonneg hX0.le hlog), Real.sq_sqrt hh.le]
      nlinarith only [show 0 ≤ D * X * X ^ a * Real.log X by positivity]
    exact hs.trans he
  have hsm := DyadicSmoothingBounds.dyadic_smoothing_bounds_with_residual hE hh hA hA
    (show X / 4 ≤ 8 * X by linarith) (show X / 8 ≤ X / 4 by linarith)
    (show 8 * X + 4 * X ^ b ≤ 16 * X by linarith)
    (show 8 * X + 2 * X ^ a ≤ 16 * X by linarith) hinc hshort
  have he : 64 * Real.sqrt D * Real.sqrt (X * Real.log X) = 8 * A := by dsimp [A]; ring
  simp only [he]
  refine ⟨hsm.1.trans (by nlinarith [Real.sqrt_nonneg (X ^ a)]), ?_⟩
  intro R hR
  have hR0 : 0 < R := hh.trans_le hR.1
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hsm.2 R hR
  refine ⟨h₁.trans (by nlinarith [Real.sqrt_nonneg R]),
    h₂.trans (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg R)),
    fun x hx => (h₃ x hx).trans (by linarith),
    h₄.trans (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg R)),
    fun x hx => (h₅ x hx).trans (div_le_div_of_nonneg_right (by linarith) hR0.le)⟩

private theorem smoothed_long_difference_bounds
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1,
        let v := fun x => doubleAverage (X ^ a) E (movingShift b t x) - doubleAverage (X ^ a) E x
        intervalL2 (X / 2) (4 * X) v ≤ C * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ b) ∧
        intervalL2 (X / 2) (4 * X) (deriv v) ≤ C * Real.sqrt (X * Real.log X) / Real.sqrt (X ^ a) ∧
        (∀ y ∈ Icc (X / 2) (4 * X), |v y| ≤
          C * Real.sqrt (X * Real.log X) * (1 + (b - a) * Real.log X)) := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := ha.trans hab
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  have hBb : ValidBand α b β := ⟨hBa.1, hBa.2.1.trans hab, hbβ, hBa.2.2.2⟩
  obtain ⟨D, hD, hsm⟩ := outer_smoothing_bounds hE hBa hab hbβ hV
  obtain ⟨M, hM, hmov⟩ := TranslationStripBounds.moving_square_bound_of_comparable
    hE hb hb1 (A := 1 / 2) (B := 4) (by norm_num) (by norm_num)
      (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBb hV)
  obtain ⟨Cb, hCb, hsb⟩ := smooth_moving_difference_outer_bounds hb hb1
  obtain ⟨Ct, hCt, hterm⟩ := terminal_moving_difference_bounds hb hb1
  obtain ⟨_, N, _, hdec⟩ := DyadicDecomposition.common_band_dyadic_decomposition hE hBa hab hbβ hV
  let L := 2 + 1 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  let T := (Ct + 2) * D * L
  have hT : 0 < T := by dsimp [T]; positivity
  let C := Real.sqrt M + 3 * D + Cb * D + T + 1
  have hC : 0 < C := by dsimp [C]; linarith [Real.sqrt_nonneg M, mul_pos hCb hD]
  have h₁ : Real.sqrt M + 2 * D ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg M, mul_pos hCb hD]
  have h₂ : Cb * D ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg M, mul_pos hCb hD]
  have h₃ : T ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg M, mul_pos hCb hD]
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsm, hmov, hsb, hterm, hdec, eventually_ge_atTop (4 : ℝ)]
    with X hsm hmov hsb hterm hdec hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  have hk : 0 < X ^ b := Real.rpow_pos_of_pos hX0 b
  have hhk : X ^ a ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le (by linarith) hab.le
  have hZ := doubleAverage_contDiff hE hh
  let A := Real.sqrt (X * Real.log X)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  let q := fun x => E x - doubleAverage (X ^ a) E x
  have hqm : Measurable q := hE.1.sub hZ.continuous.measurable
  obtain ⟨B, _, hB⟩ := hE.2 (X / 4) (8 * X)
  have hELp : MemLp E 2 (volume.restrict (Ioc (X / 4) (8 * X))) := by
    apply MemLp.of_bound hE.1.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs] using hB x ⟨hx.1.le, hx.2⟩
  have hZLp : MemLp (doubleAverage (X ^ a) E) 2 (volume.restrict (Ioc (X / 4) (8 * X))) :=
    (memLp_two_iff_integrable_sq hZ.continuous.measurable.aestronglyMeasurable).mpr
      (((hZ.continuous.pow 2).intervalIntegrable (X / 4) (8 * X)).1)
  have hqLp : MemLp q 2 (volume.restrict (Ioc (X / 4) (8 * X))) := hELp.sub hZLp
  rcases hdec with ⟨hK, hK', hN, hdecomp, _, _⟩
  let K := (2 : ℝ) ^ N X * X ^ a
  have hK0 : 0 < K := hk.trans_le hK
  have hKK : K ∈ Icc (X ^ a) (2 * X ^ b) := ⟨hhk.trans hK, hK'.le⟩
  have hKs := hsm.2 K hKK
  have hhs := hsm.2 (X ^ a) ⟨le_rfl, by linarith⟩
  intro t ht
  let z := movingIncrement E b t
  let g := fun x => q (movingShift b t x) - q x
  let v := fun x => doubleAverage (X ^ a) E (movingShift b t x) - doubleAverage (X ^ a) E x
  have hφ : Continuous (movingShift b t) :=
    continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hb.le))
  have hzm : Measurable z := (hE.1.comp hφ.measurable).sub hE.1
  have hgm : Measurable g := (hqm.comp hφ.measurable).sub hqm
  have hvm : Measurable v := (hZ.continuous.comp hφ |>.sub hZ.continuous).measurable
  have hg := measurable_moving_difference_l2_bound hb hb1 ht hX hqm hqLp
  have hzLp : MemLp z 2 (volume.restrict (Ioc (X / 2) (4 * X))) :=
    (memLp_two_iff_integrable_sq hzm.aestronglyMeasurable).mpr
      ((TranslationStripBounds.moving_sq_integrable (t := t) hE hb (X / 2) (4 * X)).1)
  have he : z - g = v := by funext x; dsimp [z, g, q, v, movingIncrement, increment, movingShift]; ring
  have hn := lpNorm_sub_le hzLp (g := g) (by norm_num : (1 : ENNReal) ≤ 2)
  rw [he,
    VarianceTransfer.lpNorm_two_eq_intervalL2 (show X / 2 ≤ 4 * X by linarith)
      hvm.aestronglyMeasurable,
    VarianceTransfer.lpNorm_two_eq_intervalL2 (show X / 2 ≤ 4 * X by linarith)
      hzm.aestronglyMeasurable,
    VarianceTransfer.lpNorm_two_eq_intervalL2 (show X / 2 ≤ 4 * X by linarith)
      hgm.aestronglyMeasurable] at hn
  have hzn : intervalL2 (X / 2) (4 * X) z ≤ Real.sqrt M * A * Real.sqrt (X ^ b) := by
    have hs := Real.sqrt_le_sqrt (hmov t ht)
    rw [show (1 / 2 : ℝ) * X = X / 2 by ring] at hs
    apply hs.trans_eq
    rw [show M * X * X ^ b * Real.log X = M * (X * Real.log X) * X ^ b by ring,
      Real.sqrt_mul (by positivity : 0 ≤ M * (X * Real.log X)), Real.sqrt_mul hM.le]
  have hgn : intervalL2 (X / 2) (4 * X) g ≤ 2 * D * A * Real.sqrt (X ^ b) := by
    apply hg.2.trans
    apply (mul_le_mul_of_nonneg_left hsm.1 (by norm_num : (0 : ℝ) ≤ 2)).trans
    have hr := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhk)
      (show 0 ≤ 2 * D * A by positivity)
    dsimp [A] at *
    nlinarith only [hr]
  have hvn : intervalL2 (X / 2) (4 * X) v ≤ C * A * Real.sqrt (X ^ b) := by
    have hle := mul_le_mul_of_nonneg_right h₁ (mul_nonneg hA (Real.sqrt_nonneg (X ^ b)))
    nlinarith only [hn, hzn, hgn, hle]
  have hvd : intervalL2 (X / 2) (4 * X) (deriv v) ≤ C * A / Real.sqrt (X ^ a) := by
    have hd := (hsb t ht (doubleAverage (X ^ a) E) hZ).2.2.trans
      (mul_le_mul_of_nonneg_left hhs.2.2.2.1 hCb.le)
    have hle := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h₂ hA) (Real.sqrt_nonneg (X ^ a))
    apply hd.trans
    exact (show Cb * (D * A / Real.sqrt (X ^ a)) = Cb * D * A / Real.sqrt (X ^ a) by ring).le.trans hle
  refine ⟨hvn, hvd, ?_⟩
  have htm := (hterm t ht (doubleAverage K E) (D * A) K (by positivity) hK
    (doubleAverage_contDiff hE hK0) hKs.2.2.2.1 hKs.2.2.2.2).2.2
  intro y hy
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have him : movingShift b t y ∈ Icc (X / 4) (8 * X) := by
    have h0 : 0 ≤ t * y ^ b := mul_nonneg ht.1 (Real.rpow_nonneg (by linarith) b)
    have h1 : t * y ^ b ≤ y :=
      (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) b) ht.2).trans
        (Real.rpow_le_self_of_one_le hy1 hb1.le)
    dsimp [movingShift]
    constructor <;> linarith [hy.1, hy.2]
  have hblock (j : ℕ) (hj : j ∈ Finset.range (N X)) :
      |smoothingBlock ((2 : ℝ) ^ j * X ^ a) E (movingShift b t y) -
        smoothingBlock ((2 : ℝ) ^ j * X ^ a) E y| ≤ 2 * D * A := by
    have hjN : j ≤ N X := (Finset.mem_range.mp hj).le
    have hR : (2 : ℝ) ^ j * X ^ a ∈ Icc (X ^ a) (2 * X ^ b) :=
      ⟨by simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hh.le,
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjN) hh.le).trans hK'.le⟩
    have hs := (hsm.2 _ hR).2.2.1
    exact (abs_sub _ _).trans ((add_le_add (hs _ him)
      (hs y ⟨by linarith [hy.1], by linarith [hy.2]⟩)).trans_eq (by dsimp [A]; ring))
  have hvsum : v y = (doubleAverage K E (movingShift b t y) - doubleAverage K E y) +
      ∑ j ∈ Finset.range (N X), (smoothingBlock ((2 : ℝ) ^ j * X ^ a) E (movingShift b t y) -
        smoothingBlock ((2 : ℝ) ^ j * X ^ a) E y) := by
    dsimp [v]
    rw [hdecomp (movingShift b t y), hdecomp y, Finset.sum_sub_distrib]
    ring
  have hsum : |v y| ≤ Ct * D * A + (N X : ℝ) * (2 * D * A) := by
    rw [hvsum]
    apply (abs_add_le _ _).trans
    have hs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hblock)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    have ht' := htm y hy
    nlinarith only [hs, ht']
  have hz : 0 ≤ (b - a) * Real.log X := mul_nonneg (sub_nonneg.mpr hab.le) hlog
  have hNL : (N X : ℝ) + 1 ≤ L * (1 + (b - a) * Real.log X) := by
    dsimp [L]
    simp only [div_eq_mul_inv] at hN ⊢
    nlinarith only [hN, hz, inv_nonneg.mpr hlog2.le]
  have hn0 : (0 : ℝ) ≤ N X := Nat.cast_nonneg _
  have hp : Ct + 2 * (N X : ℝ) ≤ (Ct + 2) * ((N X : ℝ) + 1) := by
    nlinarith only [mul_nonneg hCt.le hn0]
  have hNL' := mul_le_mul_of_nonneg_left hNL (show 0 ≤ (Ct + 2) * D * A by positivity)
  have hp' := mul_le_mul_of_nonneg_right hp (show 0 ≤ D * A by positivity)
  have hTC := mul_le_mul_of_nonneg_right h₃ (mul_nonneg hA (by linarith : 0 ≤ 1 + (b - a) * Real.log X))
  dsimp [T] at hTC
  nlinarith only [hsum, hp', hNL', hTC]

/-- Every pair of blocks between the two powers has the same short-scale covariance bound. -/
private theorem common_band_block_pair_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
      ∀ R ∈ Icc (X ^ a) (2 * X ^ b), ∀ S ∈ Icc (X ^ a) (2 * X ^ b),
        |∫ x in l..r,
          (smoothingBlock R E (movingShift a s x) - smoothingBlock R E x) *
          (smoothingBlock S E (movingShift b t x) - smoothingBlock S E x)| ≤
          C * X * X ^ a * Real.log X := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := ha.trans hab
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  obtain ⟨D, hD, hsm⟩ := outer_smoothing_bounds hE hBa hab hbβ hV
  obtain ⟨C, hC, hpair⟩ := dyadic_block_covariance_bound ha ha1 hb hb1
  have hmargin := FixedLengthCovariance.shifted_band (hBa.2.1.trans hab) hbβ hb1
    (c := 1) (d := 1) (q := 2) (r := 0) zero_lt_one zero_lt_one (by norm_num) le_rfl
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  filter_upwards [hsm, hpair, hmargin, eventually_ge_atTop (4 : ℝ)] with X hsm hpair hm hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hkX : 2 * X ^ b ≤ X := by
    simp only [fixedLength, one_mul, zero_mul, add_zero] at hm
    exact hm.2.trans (Real.rpow_le_self_of_one_le (by linarith) hBa.2.2.2.le)
  intro s hs t ht l hl r hr R hR S hS
  have hR0 : 0 < R := (Real.rpow_pos_of_pos hX0 a).trans_le hR.1
  have hS0 : 0 < S := (Real.rpow_pos_of_pos hX0 a).trans_le hS.1
  have hRu : ContDiff ℝ 1 (smoothingBlock R E) :=
    (doubleAverage_contDiff hE hR0).sub (doubleAverage_contDiff hE (by positivity : 0 < 2 * R))
  have hSu : ContDiff ℝ 1 (smoothingBlock S E) :=
    (doubleAverage_contDiff hE hS0).sub (doubleAverage_contDiff hE (by positivity : 0 < 2 * S))
  have hRsm := hsm.2 R hR
  have hSsm := hsm.2 S hS
  have hmR : intervalL2 (X / 2) (4 * X) (smoothingBlock R E) ≤
      intervalL2 (X / 4) (8 * X) (smoothingBlock R E) :=
    Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
      (show X / 4 ≤ X / 2 by linarith) (show X / 2 ≤ 4 * X by linarith)
      (show 4 * X ≤ 8 * X by linarith) (Eventually.of_forall fun _ => sq_nonneg _)
      ((hRu.continuous.pow 2).intervalIntegrable _ _))
  have hmRd : intervalL2 (X / 2) (4 * X) (deriv (smoothingBlock R E)) ≤
      intervalL2 (X / 4) (8 * X) (deriv (smoothingBlock R E)) :=
    Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
      (show X / 4 ≤ X / 2 by linarith) (show X / 2 ≤ 4 * X by linarith)
      (show 4 * X ≤ 8 * X by linarith) (Eventually.of_forall fun _ => sq_nonneg _)
      ((((contDiff_one_iff_deriv.mp hRu).2).pow 2).intervalIntegrable _ _))
  have hp := hpair s hs t ht l hl r hr (smoothingBlock R E) (smoothingBlock S E)
    (D * Real.sqrt (X * Real.log X)) R S (by positivity) hR0 hS0
    (hR.2.trans hkX) (hS.2.trans hkX) hRu hSu
    (hmR.trans hRsm.1) (hmRd.trans hRsm.2.1)
    (fun y hy => hRsm.2.2.1 y ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    hSsm.1 hSsm.2.1 hSsm.2.2.1
  apply hp.trans_eq
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hX0.le hlog)]
  ring

/-- A dyadic block pairs with the terminal double average at the short-scale cost. -/
private theorem common_band_terminal_pair_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
      ∀ K ∈ Icc (X ^ b) (2 * X ^ b), ∀ R ∈ Icc (X ^ a) K,
        |∫ x in l..r,
          (smoothingBlock R E (movingShift a s x) - smoothingBlock R E x) *
          (doubleAverage K E (movingShift b t x) - doubleAverage K E x)| ≤
          C * X * X ^ a * Real.log X := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := ha.trans hab
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  obtain ⟨D, hD, hsm⟩ := outer_smoothing_bounds hE hBa hab hbβ hV
  obtain ⟨Cv, hCv, hv⟩ := terminal_moving_difference_bounds hb hb1
  obtain ⟨Ct, hCt, htr⟩ := dyadic_transfer_pair_bound ha ha1
  have hmargin := FixedLengthCovariance.shifted_band (hBa.2.1.trans hab) hbβ hb1
    (c := 1) (d := 1) (q := 2) (r := 0) zero_lt_one zero_lt_one (by norm_num) le_rfl
  refine ⟨Ct * ((Cv + 1) * D) ^ 2, by positivity, ?_⟩
  filter_upwards [hsm, hv, htr, hmargin, eventually_ge_atTop (4 : ℝ)] with X hsm hv htr hm hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hkX : 2 * X ^ b ≤ X := by
    simp only [fixedLength, one_mul, zero_mul, add_zero] at hm
    exact hm.2.trans (Real.rpow_le_self_of_one_le (by linarith) hBa.2.2.2.le)
  intro s hs t ht l hl r hr K hK R hR
  let A := D * Real.sqrt (X * Real.log X)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA' : A ≤ (Cv + 1) * A := by nlinarith
  have hCA : Cv * A ≤ (Cv + 1) * A := by nlinarith
  have hK0 : 0 < K := (Real.rpow_pos_of_pos hX0 b).trans_le hK.1
  have hR0 : 0 < R := (Real.rpow_pos_of_pos hX0 a).trans_le hR.1
  have hRK : R ∈ Icc (X ^ a) (2 * X ^ b) := ⟨hR.1, hR.2.trans hK.2⟩
  have hKK : K ∈ Icc (X ^ a) (2 * X ^ b) :=
    ⟨(Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X) hab.le).trans hK.1, hK.2⟩
  have hRu : ContDiff ℝ 1 (smoothingBlock R E) :=
    (doubleAverage_contDiff hE hR0).sub (doubleAverage_contDiff hE (by positivity : 0 < 2 * R))
  have hKu := doubleAverage_contDiff hE hK0
  have hRsm := hsm.2 R hRK
  have hKsm := hsm.2 K hKK
  have hvm := hv t ht (doubleAverage K E) A K hA hK.1 hKu hKsm.2.2.2.1 hKsm.2.2.2.2
  let v := fun x => doubleAverage K E (movingShift b t x) - doubleAverage K E x
  have hvd : ContDiffOn ℝ 1 v (Icc (X / 2) (4 * X)) := by
    apply ContDiffOn.sub _ hKu.contDiffOn
    apply hKu.contDiffOn.comp
      (contDiffOn_id.add (contDiffOn_const.mul
        (contDiffOn_id.rpow_const_of_ne (fun x hx => by
          have : 0 < x := by linarith [hx.1]
          exact this.ne'))))
    exact fun _ _ => mem_univ _
  have huLp : MemLp (smoothingBlock R E) 2 (volume.restrict (Ioc (X / 2) (4 * X))) :=
    (memLp_two_iff_integrable_sq hRu.continuous.measurable.aestronglyMeasurable).mpr
      (((hRu.continuous.pow 2).intervalIntegrable (X / 2) (4 * X)).1)
  have hUn : intervalL2 (X / 2) (4 * X) (smoothingBlock R E) ≤ A * Real.sqrt R :=
    (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
      (show X / 4 ≤ X / 2 by linarith) (show X / 2 ≤ 4 * X by linarith)
      (show 4 * X ≤ 8 * X by linarith) (Eventually.of_forall fun _ => sq_nonneg _)
      ((hRu.continuous.pow 2).intervalIntegrable _ _))).trans hRsm.1
  have hp := htr s hs l hl r hr (smoothingBlock R E) v ((Cv + 1) * A) R K
    (by positivity) hR0 hR.2 (hK.2.trans hkX) hRu.continuous.measurable huLp hvd
    (hUn.trans (mul_le_mul_of_nonneg_right hA' (Real.sqrt_nonneg R)))
    (hvm.1.trans (mul_le_mul_of_nonneg_right hCA (Real.sqrt_nonneg K)))
    (hvm.2.1.trans (div_le_div_of_nonneg_right hCA (Real.sqrt_nonneg K)))
    (fun y hy => (hRsm.2.2.1 y ⟨by linarith [hy.1], by linarith [hy.2]⟩).trans hA')
    (fun y hy => (hvm.2.2 y hy).trans hCA)
  apply hp.trans_eq
  dsimp [A]
  rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hX0.le hlog)]
  ring

/-- The long moving difference of the small-scale residual has short-scale covariance. -/
private theorem common_band_residual_right_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
        let q := fun x => E x - doubleAverage (X ^ a) E x
        |∫ x in l..r, movingIncrement E a s x *
          (q (movingShift b t x) - q x)| ≤ C * X * X ^ a * Real.log X := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := ha.trans hab
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  obtain ⟨D, hD, hsm⟩ := outer_smoothing_bounds hE hBa hab hbβ hV
  obtain ⟨M, hM, hmov⟩ := TranslationStripBounds.moving_square_bound_of_comparable
    hE ha ha1 (A := 1) (B := 2) zero_lt_one (by norm_num)
      (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBa hV)
  refine ⟨2 * Real.sqrt M * D, by positivity, ?_⟩
  filter_upwards [hsm, hmov, eventually_ge_atTop (4 : ℝ)] with X hsm hmov hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  have hZ := doubleAverage_contDiff hE hh
  let q := fun x => E x - doubleAverage (X ^ a) E x
  have hqm : Measurable q := hE.1.sub hZ.continuous.measurable
  obtain ⟨B, _, hB⟩ := hE.2 (X / 4) (8 * X)
  have hELp : MemLp E 2 (volume.restrict (Ioc (X / 4) (8 * X))) := by
    apply MemLp.of_bound hE.1.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs] using hB x ⟨hx.1.le, hx.2⟩
  have hZLp : MemLp (doubleAverage (X ^ a) E) 2 (volume.restrict (Ioc (X / 4) (8 * X))) :=
    (memLp_two_iff_integrable_sq hZ.continuous.measurable.aestronglyMeasurable).mpr
      (((hZ.continuous.pow 2).intervalIntegrable (X / 4) (8 * X)).1)
  have hqLp : MemLp q 2 (volume.restrict (Ioc (X / 4) (8 * X))) := hELp.sub hZLp
  intro s hs t ht l hl r hr
  let f := movingIncrement E a s
  let g := fun x => q (movingShift b t x) - q x
  have hg := measurable_moving_difference_l2_bound hb hb1 ht hX hqm hqLp
  have hgm : Measurable g :=
    (hqm.comp (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hb.le))).measurable).sub hqm
  have hfm : Measurable f :=
    (hE.1.comp (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const ha.le))).measurable).sub hE.1
  have hfi := TranslationStripBounds.moving_sq_integrable (t := s) hE ha l r
  have hfLp : MemLp f 2 (volume.restrict (Ioc l r)) :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hfi.1
  have hgLp : MemLp g 2 (volume.restrict (Ioc l r)) := hg.1.mono_measure
    (Measure.restrict_mono (Ioc_subset_Ioc (by linarith [hl.1]) (by linarith [hr.2])) le_rfl)
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) _ by simpa using hfLp)
    (show MemLp g (ENNReal.ofReal 2) _ by simpa using hgLp)
  have hp : |∫ x in l..r, f x * g x| ≤ intervalL2 l r f * intervalL2 l r g := by
    have hn := (norm_integral_le_integral_norm (fun x => f x * g x)).trans
      (by simpa only [norm_mul] using hc)
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow,
      intervalIntegral.integral_of_le hr.1, intervalL2] using hn
  have hfn : intervalL2 l r f ≤ Real.sqrt M * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ a) := by
    have hm := intervalIntegral.integral_mono_interval hl.1 hr.1 hr.2
      (Eventually.of_forall fun _ => sq_nonneg _) (TranslationStripBounds.moving_sq_integrable (t := s) hE ha X (2 * X))
    have hm' := Real.sqrt_le_sqrt (hm.trans (by simpa only [one_mul] using hmov s hs))
    apply hm'.trans_eq
    rw [show M * X * X ^ a * Real.log X = M * (X * Real.log X) * X ^ a by ring,
      Real.sqrt_mul (by positivity : 0 ≤ M * (X * Real.log X)), Real.sqrt_mul hM.le]
  have hgn : intervalL2 l r g ≤ 2 * D * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ a) := by
    have hgi : IntervalIntegrable (fun x => g x ^ 2) volume (X / 2) (4 * X) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X / 2 ≤ 4 * X)]
      exact hg.1.integrable_sq
    apply (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
      (show X / 2 ≤ l by linarith [hl.1]) hr.1 (show r ≤ 4 * X by linarith [hr.2])
      (Eventually.of_forall fun _ => sq_nonneg _) hgi)).trans
    apply hg.2.trans
    exact (mul_le_mul_of_nonneg_left hsm.1 (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  apply (hp.trans (mul_le_mul hfn hgn (Real.sqrt_nonneg _) (by positivity))).trans_eq
  calc
    _ = 2 * Real.sqrt M * D * (Real.sqrt (X * Real.log X)) ^ 2 * (Real.sqrt (X ^ a)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (mul_nonneg hX0.le hlog), Real.sq_sqrt hh.le]; ring

private theorem residual_left_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
        let q := fun x => E x - doubleAverage (X ^ a) E x
        |∫ x in l..r, (q (movingShift a s x) - q x) *
          (doubleAverage (X ^ a) E (movingShift b t x) - doubleAverage (X ^ a) E x)| ≤
          C * X * X ^ a * Real.log X * (1 + (b - a) * Real.log X) := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  obtain ⟨D, hD, hsm⟩ := outer_smoothing_bounds hE hBa hab hbβ hV
  obtain ⟨V, hV0, hv⟩ := smoothed_long_difference_bounds hE hBa hab hbβ hV
  obtain ⟨C, hC, ht⟩ := residual_transfer_pair_bound ha ha1
  refine ⟨C * (D + V) ^ 2, by positivity, ?_⟩
  filter_upwards [hsm, hv, ht, eventually_ge_atTop (4 : ℝ)] with X hsm hv ht hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  have hk : 0 < X ^ b := Real.rpow_pos_of_pos hX0 b
  let A := Real.sqrt (X * Real.log X)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  let q := fun x => E x - doubleAverage (X ^ a) E x
  have hZ := doubleAverage_contDiff hE hh
  have hqm : Measurable q := hE.1.sub hZ.continuous.measurable
  obtain ⟨B, _, hB⟩ := hE.2 (X / 4) (8 * X)
  have hELp : MemLp E 2 (volume.restrict (Ioc (X / 4) (8 * X))) := by
    apply MemLp.of_bound hE.1.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simpa only [Real.norm_eq_abs] using hB x ⟨hx.1.le, hx.2⟩
  have hZLp : MemLp (doubleAverage (X ^ a) E) 2 (volume.restrict (Ioc (X / 4) (8 * X))) :=
    (memLp_two_iff_integrable_sq hZ.continuous.measurable.aestronglyMeasurable).mpr
      (((hZ.continuous.pow 2).intervalIntegrable (X / 4) (8 * X)).1)
  have hqLp : MemLp q 2 (volume.restrict (Ioc (X / 4) (8 * X))) := hELp.sub hZLp
  have hqnorm : intervalL2 (X / 2) (4 * X) q ≤ D * A * Real.sqrt (X ^ a) := by
    have hi : IntervalIntegrable (fun x => q x ^ 2) volume (X / 4) (8 * X) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X / 4 ≤ 8 * X)]
      exact hqLp.integrable_sq
    exact (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
      (show X / 4 ≤ X / 2 by linarith) (show X / 2 ≤ 4 * X by linarith)
      (show 4 * X ≤ 8 * X by linarith) (Eventually.of_forall fun _ => sq_nonneg _) hi)).trans hsm.1
  have hprod : Real.sqrt (X ^ a) * Real.sqrt (X ^ b) ≤ X := by
    rw [← Real.sqrt_mul hh.le]
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hX0.le, (mul_le_mul
      (Real.rpow_le_self_of_one_le (by linarith) ha1.le)
      (Real.rpow_le_self_of_one_le (by linarith) hb1.le) hk.le hX0.le).trans_eq (by ring)⟩
  have hDV : D * A ≤ (D + V) * A := by nlinarith
  have hVV : V * A ≤ (D + V) * A := by nlinarith
  intro s hs t ht' l hl r hr
  let v := fun x => doubleAverage (X ^ a) E (movingShift b t x) - doubleAverage (X ^ a) E x
  have hvd : ContDiffOn ℝ 1 v (Icc (X / 2) (4 * X)) := by
    apply ContDiffOn.sub _ hZ.contDiffOn
    apply hZ.contDiffOn.comp
      (contDiffOn_id.add (contDiffOn_const.mul
        (contDiffOn_id.rpow_const_of_ne (fun x hx => by
          have : 0 < x := by linarith [hx.1]
          exact this.ne'))))
    exact fun _ _ => mem_univ _
  have hn : 1 ≤ 1 + (b - a) * Real.log X := by nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) hlog]
  have hp := ht s hs l hl r hr q v ((D + V) * A) (X ^ b)
    (1 + (b - a) * Real.log X) (by positivity) hk hprod hn hqm
    (hqLp.mono_measure (Measure.restrict_mono
      (Ioc_subset_Ioc (by linarith) (by linarith)) le_rfl)) hvd
    (hqnorm.trans (mul_le_mul_of_nonneg_right hDV (Real.sqrt_nonneg _)))
    ((hv t ht').1.trans (mul_le_mul_of_nonneg_right hVV (Real.sqrt_nonneg _)))
    ((hv t ht').2.1.trans (div_le_div_of_nonneg_right hVV (Real.sqrt_nonneg _)))
    (fun y hy => ((hv t ht').2.2 y hy).trans (mul_le_mul_of_nonneg_right hVV (by linarith)))
  apply hp.trans_eq
  dsimp [A]
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hX0.le hlog)]
  ring

private theorem terminal_first_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
      ∀ K ∈ Icc (X ^ b) (2 * X ^ b),
        |∫ x in l..r, (doubleAverage K E (movingShift a s x) - doubleAverage K E x) *
          (doubleAverage (X ^ a) E (movingShift b t x) - doubleAverage (X ^ a) E x)| ≤
          C * X * X ^ a * Real.log X := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := ha.trans hab
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  obtain ⟨D, hD, hsm⟩ := outer_smoothing_bounds hE hBa hab hbβ hV
  obtain ⟨V, hV0, hv⟩ := smoothed_long_difference_bounds hE hBa hab hbβ hV
  obtain ⟨Ca, hCa, hsa⟩ := SmoothMovingDifference.smooth_moving_difference_bounds ha ha1
  refine ⟨Ca * D * V, by positivity, ?_⟩
  filter_upwards [hsm, hv, hsa, eventually_ge_atTop (4 : ℝ)] with X hsm hv hsa hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  have hk : 0 < X ^ b := Real.rpow_pos_of_pos hX0 b
  intro s hs t ht l hl r hr K hK
  have hK0 : 0 < K := hk.trans_le hK.1
  have hKu := doubleAverage_contDiff hE hK0
  have hhu := doubleAverage_contDiff hE hh
  let f := fun x => doubleAverage K E (movingShift a s x) - doubleAverage K E x
  let v := fun x => doubleAverage (X ^ a) E (movingShift b t x) - doubleAverage (X ^ a) E x
  have hf : Continuous f := hKu.continuous.comp
    (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const ha.le))) |>.sub hKu.continuous
  have hvc : Continuous v := hhu.continuous.comp
    (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hb.le))) |>.sub hhu.continuous
  have hKK : K ∈ Icc (X ^ a) (2 * X ^ b) :=
    ⟨(Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X) hab.le).trans hK.1, hK.2⟩
  have hKd : intervalL2 (X / 2) (4 * X) (deriv (doubleAverage K E)) ≤
      D * Real.sqrt (X * Real.log X) / Real.sqrt K := by
    exact (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
      (show X / 4 ≤ X / 2 by linarith) (show X / 2 ≤ 4 * X by linarith)
      (show 4 * X ≤ 8 * X by linarith) (Eventually.of_forall fun _ => sq_nonneg _)
      ((((contDiff_one_iff_deriv.mp hKu).2).pow 2).intervalIntegrable _ _))).trans
      (hsm.2 K hKK).2.2.2.1
  have hfn : intervalL2 l r f ≤ Ca * X ^ a * (D * Real.sqrt (X * Real.log X) / Real.sqrt K) :=
    (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval hl.1 hr.1 hr.2
      (Eventually.of_forall fun _ => sq_nonneg _) ((hf.pow 2).intervalIntegrable X (2 * X)))).trans
      (((hsa s hs (doubleAverage K E) hKu.contDiffOn).1).trans
        (mul_le_mul_of_nonneg_left hKd (by positivity)))
  have hvn : intervalL2 l r v ≤ V * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ b) :=
    (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
      (show X / 2 ≤ l by linarith [hl.1]) hr.1 (show r ≤ 4 * X by linarith [hr.2])
      (Eventually.of_forall fun _ => sq_nonneg _) ((hvc.pow 2).intervalIntegrable _ _))).trans (hv t ht).1
  have hfi : MemLp f 2 (volume.restrict (Ioc l r)) :=
    (memLp_two_iff_integrable_sq hf.measurable.aestronglyMeasurable).mpr (((hf.pow 2).intervalIntegrable l r).1)
  have hvi : MemLp v 2 (volume.restrict (Ioc l r)) :=
    (memLp_two_iff_integrable_sq hvc.measurable.aestronglyMeasurable).mpr (((hvc.pow 2).intervalIntegrable l r).1)
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) _ by simpa using hfi)
    (show MemLp v (ENNReal.ofReal 2) _ by simpa using hvi)
  have hp : |∫ x in l..r, f x * v x| ≤ intervalL2 l r f * intervalL2 l r v := by
    have hn := (norm_integral_le_integral_norm (fun x => f x * v x)).trans
      (by simpa only [norm_mul] using hc)
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow,
      intervalIntegral.integral_of_le hr.1, intervalL2] using hn
  have hratio : Real.sqrt (X ^ b) / Real.sqrt K ≤ 1 :=
    (div_le_one (Real.sqrt_pos.mpr hK0)).mpr (Real.sqrt_le_sqrt hK.1)
  calc
    _ ≤ (Ca * X ^ a * (D * Real.sqrt (X * Real.log X) / Real.sqrt K)) *
        (V * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ b)) :=
      hp.trans (mul_le_mul hfn hvn (Real.sqrt_nonneg _) (by positivity))
    _ = (Ca * D * V * X * X ^ a * Real.log X) * (Real.sqrt (X ^ b) / Real.sqrt K) := by
      rw [show (Ca * X ^ a * (D * Real.sqrt (X * Real.log X) / Real.sqrt K)) *
        (V * Real.sqrt (X * Real.log X) * Real.sqrt (X ^ b)) =
        Ca * D * V * (Real.sqrt (X * Real.log X)) ^ 2 * X ^ a * (Real.sqrt (X ^ b) / Real.sqrt K) by ring,
        Real.sq_sqrt (mul_nonneg hX0.le hlog)]
      ring
    _ ≤ _ := by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ Ca * D * V * X * X ^ a * Real.log X by positivity))

/-- A common variance band controls all subinterval covariances of the two moving increments. -/
theorem common_band_covariance_bound
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
        |∫ x in l..r, movingIncrement E a s x * movingIncrement E b t x| ≤
          C * X * X ^ a * Real.log X * (1 + (b - a) * Real.log X) ^ 2 := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := ha.trans hab
  obtain ⟨C₀, hC₀, h₀⟩ := common_band_residual_right_bound hE hBa hab hbβ hV
  obtain ⟨C₁, hC₁, h₁⟩ := residual_left_bound hE hBa hab hbβ hV
  obtain ⟨C₂, hC₂, h₂⟩ := terminal_first_bound hE hBa hab hbβ hV
  obtain ⟨C₃, hC₃, h₃⟩ := common_band_terminal_pair_bound hE hBa hab hbβ hV
  obtain ⟨C₄, hC₄, h₄⟩ := common_band_block_pair_bound hE hBa hab hbβ hV
  obtain ⟨_, N, _, hd⟩ := DyadicDecomposition.common_band_dyadic_decomposition hE hBa hab hbβ hV
  let L := 2 + 1 / Real.log 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 1 ≤ L := by dsimp [L]; have := inv_nonneg.mpr hl2.le; simp only [one_div]; linarith
  refine ⟨(C₀ + C₁ + C₂ + C₃ + C₄) * (L + 1) ^ 2, by positivity, ?_⟩
  filter_upwards [h₀, h₁, h₂, h₃, h₄, hd, eventually_ge_atTop (4 : ℝ)]
    with X h₀ h₁ h₂ h₃ h₄ hd hX
  have hX0 : 0 < X := by linarith
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  have hk : 0 < X ^ b := Real.rpow_pos_of_pos hX0 b
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  let B := X * X ^ a * Real.log X
  let Q := 1 + (b - a) * Real.log X
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith only [mul_nonneg (sub_nonneg.mpr hab.le) hlog]
  rcases hd with ⟨hK, hK', hN, hdecomp, _, _⟩
  let K := (2 : ℝ) ^ N X * X ^ a
  let Zh := doubleAverage (X ^ a) E
  let ZK := doubleAverage K E
  let q := fun x => E x - Zh x
  let U := fun (θ c : ℝ) (u : ℝ → ℝ) (x : ℝ) => u (movingShift θ c x) - u x
  let blocks := fun j : ℕ => smoothingBlock ((2 : ℝ) ^ j * X ^ a) E
  have hK0 : 0 < K := hk.trans_le hK
  have hKK : K ∈ Icc (X ^ b) (2 * X ^ b) := ⟨hK, hK'.le⟩
  have hR (j : ℕ) (_hj : j ∈ Finset.range (N X)) : (2 : ℝ) ^ j * X ^ a ∈ Icc (X ^ a) K :=
    ⟨by simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hh.le,
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Finset.mem_range.mp _hj).le) hh.le⟩
  have hBR (j : ℕ) (hj : j ∈ Finset.range (N X)) : (2 : ℝ) ^ j * X ^ a ∈ Icc (X ^ a) (2 * X ^ b) :=
    ⟨(hR j hj).1, (hR j hj).2.trans hK'.le⟩
  have hU (θ c x : ℝ) : U θ c Zh x = U θ c ZK x +
      ∑ j ∈ Finset.range (N X), U θ c (blocks j) x := by
    dsimp [U, Zh, ZK, blocks]
    rw [hdecomp (movingShift θ c x), hdecomp x, Finset.sum_sub_distrib]
    ring
  have hc (θ c : ℝ) (hθ : 0 < θ) (u : ℝ → ℝ) (hu : Continuous u) : Continuous (U θ c u) :=
    hu.comp (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hθ.le))) |>.sub hu
  have hZh := (doubleAverage_contDiff hE hh).continuous
  have hZK := (doubleAverage_contDiff hE hK0).continuous
  have hbcont (j : ℕ) (hj : j ∈ Finset.range (N X)) : Continuous (blocks j) :=
    ((doubleAverage_contDiff hE (hh.trans_le (hR j hj).1)).sub
      (doubleAverage_contDiff hE (by have := hh.trans_le (hR j hj).1; positivity))).continuous
  intro s hs t ht l hl r hr
  let F := movingIncrement E a s
  let z := movingIncrement E b t
  let v := U b t Zh
  let p₀ := fun x => F x * U b t q x
  let p₁ := fun x => U a s q x * v x
  let p₂ := fun x => U a s ZK x * v x
  let p₃ := fun j x => U a s (blocks j) x * U b t ZK x
  let p₄ := fun j i x => U a s (blocks j) x * U b t (blocks i) x
  have hLp (u : ℝ → ℝ) (hu : Continuous u) : MemLp u 2 (volume.restrict (Ioc l r)) :=
    (memLp_two_iff_integrable_sq hu.measurable.aestronglyMeasurable).mpr (((hu.pow 2).intervalIntegrable l r).1)
  have hmoving (θ c : ℝ) (hθ : 0 < θ) : MemLp (movingIncrement E θ c) 2 (volume.restrict (Ioc l r)) :=
    (memLp_two_iff_integrable_sq
      (((hE.1.comp (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hθ.le))).measurable).sub hE.1).aestronglyMeasurable)).mpr
      ((TranslationStripBounds.moving_sq_integrable (t := c) hE hθ l r).1)
  have hIq (θ c : ℝ) (hθ : 0 < θ) : MemLp (U θ c q) 2 (volume.restrict (Ioc l r)) := by
    have he : U θ c q = movingIncrement E θ c - U θ c Zh := by
      funext x; dsimp [U, q, movingIncrement, increment, movingShift]; ring
    rw [he]; exact (hmoving θ c hθ).sub (hLp _ (hc θ c hθ Zh hZh))
  have hi (f g : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioc l r)))
      (hg : MemLp g 2 (volume.restrict (Ioc l r))) : IntervalIntegrable (fun x => f x * g x) volume l r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1]; exact hf.integrable_mul hg
  have hp := finite_covariance_expansion_bound
    (hi F (U b t q) (hmoving a s ha) (hIq b t hb))
    (hi (U a s q) v (hIq a s ha) (hLp _ (hc b t hb Zh hZh)))
    ((hc a s ha ZK hZK).mul (hc b t hb Zh hZh) |>.intervalIntegrable l r)
    (fun j hj => ((hc a s ha _ (hbcont j hj)).mul (hc b t hb ZK hZK)).intervalIntegrable l r)
    (fun j hj i hi => ((hc a s ha _ (hbcont j hj)).mul (hc b t hb _ (hbcont i hi))).intervalIntegrable l r)
    (F := fun x => F x * z x) (p₀ := p₀) (p₁ := p₁) (p₂ := p₂) (p₃ := p₃) (p₄ := p₄)
    (by
      intro x _
      have he : F x * z x = p₀ x + p₁ x + U a s Zh x * v x := by
        dsimp [F, z, p₀, p₁, U, q, v, movingIncrement, increment, movingShift]; ring
      rw [he, hU a s x, add_mul]
      have hes : (∑ j ∈ Finset.range (N X), U a s (blocks j) x) * v x =
          ∑ j ∈ Finset.range (N X), p₃ j x +
          ∑ j ∈ Finset.range (N X), ∑ i ∈ Finset.range (N X), p₄ j i x := by
        dsimp [v]; rw [hU b t x]
        simp only [p₃, p₄, mul_add, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      rw [hes]; dsimp [p₂]; ring)
    (show |∫ x in l..r, p₀ x| ≤ C₀ * B by simpa [p₀, F, U, q, Zh, B, mul_assoc] using h₀ s hs t ht l hl r hr)
    (show |∫ x in l..r, p₁ x| ≤ C₁ * B * Q by simpa [p₁, U, q, v, Zh, B, Q, mul_assoc] using h₁ s hs t ht l hl r hr)
    (show |∫ x in l..r, p₂ x| ≤ C₂ * B by simpa [p₂, U, v, ZK, Zh, B, mul_assoc] using h₂ s hs t ht l hl r hr K hKK)
    (fun j hj => by simpa [p₃, U, blocks, ZK, B, mul_assoc] using h₃ s hs t ht l hl r hr K hKK _ (hR j hj))
    (fun j hj i hi => by simpa [p₄, U, blocks, B, mul_assoc] using h₄ s hs t ht l hl r hr _ (hBR j hj) _ (hBR i hi))
  have hn : (N X : ℝ) ≤ L * Q := by
    dsimp [L, Q]; simp only [div_eq_mul_inv] at hN ⊢
    nlinarith only [hN, mul_nonneg (sub_nonneg.mpr hab.le) hlog, inv_nonneg.mpr hl2.le]
  let W := (L + 1) * Q
  have hW : 1 ≤ W := by dsimp [W]; nlinarith only [hL, hQ, mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ Q)]
  have hQW : Q ≤ W := by dsimp [W]; nlinarith only [mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ Q)]
  have hnW : (N X : ℝ) ≤ W := hn.trans (by dsimp [W]; nlinarith only [hQ])
  have hn0 : (0 : ℝ) ≤ N X := Nat.cast_nonneg _
  have hw2 : 1 ≤ W ^ 2 := by nlinarith only [hW]
  have hq2 : Q ≤ W ^ 2 := by nlinarith only [hQW, hW]
  have hn2 : (N X : ℝ) ≤ W ^ 2 := by nlinarith only [hnW, hW]
  have hnn2 : (N X : ℝ) ^ 2 ≤ W ^ 2 := (sq_le_sq₀ hn0 (by linarith)).mpr hnW
  apply hp.trans
  have hbound : C₀ * B + C₁ * B * Q + C₂ * B + (N X : ℝ) * (C₃ * B) + (N X : ℝ) ^ 2 * (C₄ * B) ≤
      (C₀ + C₁ + C₂ + C₃ + C₄) * B * W ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hw2 (mul_nonneg hC₀.le hB),
      mul_le_mul_of_nonneg_left hq2 (mul_nonneg hC₁.le hB),
      mul_le_mul_of_nonneg_left hw2 (mul_nonneg hC₂.le hB),
      mul_le_mul_of_nonneg_left hn2 (mul_nonneg hC₃.le hB),
      mul_le_mul_of_nonneg_left hnn2 (mul_nonneg hC₄.le hB)]
  convert hbound using 1 <;> dsimp [B, W, Q] <;> ring

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandCovariance
