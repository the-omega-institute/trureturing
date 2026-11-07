/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaging comparable increments bounds moving increments uniformly in the profile parameter. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Uniform square bounds for the increments with length `s x^θ`. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingIncrementVariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer MovingLengthVariance

noncomputable section

private lemma moving_shift_integral_le {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {θ X s : ℝ}
    (hθ : 0 < θ) (hX : 1 ≤ X) (hs : 0 ≤ s)
    (hbound : ∀ x ∈ Icc X (2 * X), x + s * x ^ θ ≤ 3 * X) (w : ℝ) :
    (∫ x in X..(2 * X), increment E w (x + s * x ^ θ) ^ 2) ≤
      cumulativeVariance E (3 * X) w := by
  let φ : ℝ → ℝ := fun x => x + s * x ^ θ
  let φ' : ℝ → ℝ := fun x => 1 + s * (θ * x ^ (θ - 1))
  have hc : Continuous φ := continuous_id.add
    (continuous_const.mul (Real.continuous_rpow_const hθ.le))
  have hd : ∀ x ∈ Icc X (2 * X), HasDerivWithinAt φ (φ' x) (Icc X (2 * X)) x := by
    intro x hx
    exact ((hasDerivAt_id x).add
      ((Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : x ≠ 0))).const_mul s)).hasDerivWithinAt
  have hder : ∀ x ∈ Icc X (2 * X), 1 ≤ φ' x := by
    intro x hx
    dsimp [φ']
    have hx0 : 0 < x := by linarith [hx.1]
    have : 0 ≤ s * (θ * x ^ (θ - 1)) := by positivity
    linarith
  have hinj : InjOn φ (Icc X (2 * X)) := by
    apply StrictMonoOn.injOn
    intro x hx y hy hxy
    have hpow := Real.rpow_le_rpow (by linarith [hx.1] : 0 ≤ x) hxy.le hθ.le
    exact add_lt_add_of_lt_of_le hxy (mul_le_mul_of_nonneg_left hpow hs)
  have hsub : φ '' Icc X (2 * X) ⊆ Icc (1 : ℝ) (3 * X) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 < x := by linarith [hx.1]
    exact ⟨by dsimp [φ]; nlinarith [Real.rpow_pos_of_pos hx0 θ, hx.1], hbound x hx⟩
  have hi : IntegrableOn (fun y => increment E w y ^ 2) (Icc (1 : ℝ) (3 * X)) := by
    simpa only [pow_two, id_eq] using
      increment_product_comp_integrableOn hE isCompact_Icc
        continuous_const continuous_id continuous_const continuous_id
  have himage := hi.mono_set hsub
  have hiweighted := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Icc hd hinj (fun y => increment E w y ^ 2)).mp himage
  have hiφ : IntegrableOn (fun x => increment E w (φ x) ^ 2) (Icc X (2 * X)) := by
    simpa only [pow_two] using increment_product_comp_integrableOn hE isCompact_Icc
      continuous_const hc continuous_const hc
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Icc hd hinj (fun y => increment E w y ^ 2)
  calc
    _ = ∫ x in Icc X (2 * X), increment E w (φ x) ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : X ≤ 2 * X)]
    _ ≤ ∫ x in Icc X (2 * X), |φ' x| • increment E w (φ x) ^ 2 := by
      apply setIntegral_mono_on hiφ hiweighted measurableSet_Icc
      intro x hx
      rw [smul_eq_mul, abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (hder x hx))]
      exact le_mul_of_one_le_left (sq_nonneg _) (hder x hx)
    _ = ∫ y in φ '' Icc X (2 * X), increment E w y ^ 2 := hchange.symm
    _ ≤ ∫ y in Icc (1 : ℝ) (3 * X), increment E w y ^ 2 :=
      setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall hsub)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ 3 * X)]
      rfl

private lemma averaged_increment_square_le {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {h L : ℝ} (hh : 0 < h)
    (hL : L ∈ Icc (0 : ℝ) (2 * h)) (x : ℝ) :
    h * increment E L x ^ 2 ≤
      2 * (∫ v in (3 * h)..(4 * h), increment E v x ^ 2) +
      2 * (∫ w in h..(4 * h), increment E w (x + L) ^ 2) := by
  have hi (a b y : ℝ) : IntervalIntegrable (fun v => increment E v y ^ 2) volume a b := by
    simpa only [pow_two, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_id continuous_const continuous_id continuous_const).intervalIntegrable
  have hishift : IntervalIntegrable (fun v => increment E (v - L) (x + L) ^ 2)
      volume (3 * h) (4 * h) := by
    simpa only [pow_two, Pi.sub_apply, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        (continuous_id.sub continuous_const) continuous_const
        (continuous_id.sub continuous_const) continuous_const).intervalIntegrable
  have hpoint (v : ℝ) : increment E L x ^ 2 ≤
      2 * increment E v x ^ 2 + 2 * increment E (v - L) (x + L) ^ 2 := by
    have hid : increment E L x = increment E v x - increment E (v - L) (x + L) := by
      unfold increment
      rw [show x + L + (v - L) = x + v by ring]
      ring
    rw [hid]
    simpa only [sub_eq_add_neg, neg_sq, mul_add] using
      (add_sq_le (a := increment E v x) (b := -increment E (v - L) (x + L)))
  have hm := intervalIntegral.integral_mono_on (by linarith : 3 * h ≤ 4 * h)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => increment E L x ^ 2)
      volume (3 * h) (4 * h))
    (((hi _ _ _).const_mul 2).add (hishift.const_mul 2)) (fun v _ => hpoint v)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    ((hi _ _ _).const_mul 2) (hishift.const_mul 2)] at hm
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul] at hm
  have htrans : (∫ v in (3 * h)..(4 * h), increment E (v - L) (x + L) ^ 2) =
      ∫ w in (3 * h - L)..(4 * h - L), increment E w (x + L) ^ 2 := by
    simpa only [sub_eq_add_neg] using intervalIntegral.integral_comp_add_right
      (fun w : ℝ => increment E w (x + L) ^ 2) (-L)
  have hmono := intervalIntegral.integral_mono_interval (by linarith [hL.2] : h ≤ 3 * h - L)
    (by linarith : 3 * h - L ≤ 4 * h - L) (by linarith [hL.1] : 4 * h - L ≤ 4 * h)
    (Eventually.of_forall (fun _ => sq_nonneg _)) (hi h (4 * h) (x + L))
  rw [htrans] at hm
  nlinarith

/-- The moving-increment square bound has a threshold independent of its parameter in `[0,1]`. -/
theorem moving_increment_square_bound {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
        (∫ x in X..(2 * X), increment E (s * x ^ θ) x ^ 2) ≤
          C * X * X ^ θ * Real.log X := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hpow : Continuous (fun x : ℝ => x ^ θ) := Real.continuous_rpow_const hθ0.le
  obtain ⟨K, hK, hKv⟩ := comparable_length_variance_bound hE hB hV
    (A := 1) (B := 4) (d := 3) (by norm_num) (by norm_num) (by norm_num)
  have hband := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ1
    (c := 1) (d := 1) (q := 2) (r := 0) zero_lt_one zero_lt_one (by norm_num) le_rfl
  refine ⟨8 * K, by positivity, ?_⟩
  filter_upwards [hKv, hband, eventually_ge_atTop (1 : ℝ)] with X hKv hband hX
  simp only [one_mul] at hKv
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hXX : X ≤ 2 * X := by linarith
  let h := X ^ θ
  have hh : 0 < h := Real.rpow_pos_of_pos hX0 θ
  have h2h : 2 * h ≤ X := by
    simp only [fixedLength, one_mul, zero_mul, add_zero] at hband
    exact hband.2.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX hB.2.2.2.le)
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  let φ : ℝ → ℝ := fun x => x + s * x ^ θ
  have hφ : Continuous φ := continuous_id.add (continuous_const.mul hpow)
  have hL : ∀ x ∈ Icc X (2 * X), s * x ^ θ ∈ Icc (0 : ℝ) (2 * h) := by
    intro x hx
    have hx0 : 0 < x := hX0.trans_le hx.1
    refine ⟨by positivity, ?_⟩
    calc
      s * x ^ θ ≤ x ^ θ := mul_le_of_le_one_left (Real.rpow_pos_of_pos hx0 θ).le hs.2
      _ ≤ (2 * X) ^ θ := Real.rpow_le_rpow hx0.le hx.2 hθ0.le
      _ = (2 : ℝ) ^ θ * h := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ 2 * h := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1.le
  have hφbound : ∀ x ∈ Icc X (2 * X), x + s * x ^ θ ≤ 3 * X := by
    intro x hx
    linarith [(hL x hx).2, hx.2]
  have hi (v a b : ℝ) : IntervalIntegrable (fun x => increment E v x ^ 2) volume a b := by
    simpa only [pow_two, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hr1 := increment_sq_rectangle_integrable hE X (2 * X) (3 * h) (4 * h)
    (u := fun p => p.2) continuous_snd
  have hr2 : Integrable (fun p : ℝ × ℝ => increment E p.2 (φ p.1) ^ 2)
      ((volume.restrict (Ioc X (2 * X))).prod (volume.restrict (Ioc h (4 * h)))) := by
    rw [Measure.prod_restrict]
    have hi := increment_product_comp_integrableOn (μ := volume.prod volume) hE
      (K := Icc X (2 * X) ×ˢ Icc h (4 * h)) (isCompact_Icc.prod isCompact_Icc)
      continuous_snd (hφ.comp continuous_fst) continuous_snd (hφ.comp continuous_fst)
    simpa only [pow_two, IntegrableOn, Function.comp_apply] using
      hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hi1 : IntervalIntegrable (fun x =>
      ∫ v in (3 * h)..(4 * h), increment E v x ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXX]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le (by linarith : 3 * h ≤ 4 * h)]
      using hr1.integral_prod_left
  have hi2 : IntervalIntegrable (fun x =>
      ∫ w in h..(4 * h), increment E w (φ x) ^ 2) volume X (2 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXX]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le (by linarith : h ≤ 4 * h)]
      using hr2.integral_prod_left
  have hfirst : (∫ x in X..(2 * X),
      ∫ v in (3 * h)..(4 * h), increment E v x ^ 2) ≤
        h * (K * X * h * Real.log X) := by
    simp_rw [intervalIntegral.integral_of_le hXX,
      intervalIntegral.integral_of_le (by linarith : 3 * h ≤ 4 * h)]
    rw [integral_integral_swap hr1]
    calc
      _ ≤ ∫ _v in Ioc (3 * h) (4 * h), K * X * h * Real.log X := by
        apply setIntegral_mono_on hr1.integral_prod_right (integrableOn_const (by simp))
          measurableSet_Ioc
        intro v hv
        have hsub : (∫ x in X..(2 * X), increment E v x ^ 2) ≤
            cumulativeVariance E (3 * X) v :=
          intervalIntegral.integral_mono_interval hX hXX (by linarith)
            (Eventually.of_forall (fun _ => sq_nonneg _)) (hi _ _ _)
        rw [← intervalIntegral.integral_of_le hXX]
        exact hsub.trans (hKv v ⟨by linarith [hv.1], hv.2⟩)
      _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ 4 * h - 3 * h), smul_eq_mul]
        ring
  have hsecond : (∫ x in X..(2 * X),
      ∫ w in h..(4 * h), increment E w (φ x) ^ 2) ≤
        3 * h * (K * X * h * Real.log X) := by
    simp_rw [intervalIntegral.integral_of_le hXX,
      intervalIntegral.integral_of_le (by linarith : h ≤ 4 * h)]
    rw [integral_integral_swap hr2]
    calc
      _ ≤ ∫ _w in Ioc h (4 * h), K * X * h * Real.log X := by
        apply setIntegral_mono_on hr2.integral_prod_right (integrableOn_const (by simp))
          measurableSet_Ioc
        intro w hw
        rw [← intervalIntegral.integral_of_le hXX]
        exact (moving_shift_integral_le hE hθ0 hX hs.1 hφbound w).trans
          (hKv w ⟨hw.1.le, hw.2⟩)
      _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ 4 * h - h), smul_eq_mul]
        ring
  have himoving : IntervalIntegrable (fun x => increment E (s * x ^ θ) x ^ 2)
      volume X (2 * X) := by
    simpa only [pow_two, id_eq, Pi.mul_apply] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        (continuous_const.mul hpow) continuous_id
        (continuous_const.mul hpow) continuous_id).intervalIntegrable
  have hm := intervalIntegral.integral_mono_on hXX (himoving.const_mul h)
    ((hi1.const_mul 2).add (hi2.const_mul 2))
    (fun x hx => averaged_increment_square_le hE hh (hL x hx) x)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi1.const_mul 2) (hi2.const_mul 2)] at hm
  simp only [intervalIntegral.integral_const_mul] at hm
  have htotal : h * (∫ x in X..(2 * X), increment E (s * x ^ θ) x ^ 2) ≤
      h * (8 * K * X * h * Real.log X) := by linarith
  exact le_of_mul_le_mul_left htotal hh

end
end D5.S3.Arith.Robin.ForwardKernel.MovingIncrementVariance
