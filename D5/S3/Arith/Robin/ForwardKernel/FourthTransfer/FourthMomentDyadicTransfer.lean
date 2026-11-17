/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentDyadicTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous fixed-scale mixed moments give dyadic moment interfaces. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentMovingTransfer
import D5.S3.Arith.Robin.ForwardKernel.FirstOrderInterface
import D5.S3.Arith.Robin.ForwardKernel.SecondOrderInterface
import D5.S3.Arith.Robin.ForwardKernel.DyadicMacroMoments
import D5.S3.Arith.Robin.ForwardKernel.BrownianFourthKernel
import D5.S3.Arith.Robin.ForwardKernel.MomentTransferWeights

/-! Uniform logarithmic correction and the exact dyadic normalization. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentDyadicTransfer

open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
open VarianceTransferDefs MomentTransferDefs DyadicProbability
open MacroscopicVarianceDefs FourthMomentTransferDefs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma logarithmic_correction_bounds {X x : ℝ} (hX : 4 ≤ X)
    (hx : x ∈ Icc X (2 * X)) :
    0 ≤ Real.sqrt (Real.log X / Real.log x) ∧
    Real.sqrt (Real.log X / Real.log x) ≤ 1 ∧
    |Real.sqrt (Real.log X / Real.log x) - 1| ≤ Real.log 2 / Real.log X := by
  obtain ⟨hL, he⟩ := MomentTransferWeights.logarithmic_factor_bounds hX hx.1 hx.2
  have hXlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
  have hinv : Real.sqrt (Real.log X / Real.log x) =
      (Real.sqrt (Real.log x / Real.log X))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  rw [hinv]
  have hLpos : 0 < Real.sqrt (Real.log x / Real.log X) := by linarith
  have hi : (Real.sqrt (Real.log x / Real.log X))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hL
  refine ⟨inv_nonneg.mpr hLpos.le, hi, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hi)]
  have herr : 1 - (Real.sqrt (Real.log x / Real.log X))⁻¹ ≤
      Real.sqrt (Real.log x / Real.log X) - 1 := by
    apply (mul_le_mul_iff_left₀ hLpos).mp
    field_simp
    nlinarith [sq_nonneg (Real.sqrt (Real.log x / Real.log X) - 1)]
  linarith

/-- Every fixed power of the logarithmic correction tends uniformly to one on a dyadic interval. -/
theorem logarithmic_correction_eventually (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ x ∈ Icc X (2 * X),
      |Real.sqrt (Real.log X / Real.log x) ^ k - 1| < η := by
  have ht : Tendsto (fun X : ℝ => (Real.log 2 / Real.log X) * (k : ℝ))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).mul_const (k : ℝ)
  filter_upwards [eventually_ge_atTop (4 : ℝ), ht.eventually (gt_mem_nhds hη)] with X hX he
  intro x hx
  obtain ⟨h0, h1, hb⟩ := logarithmic_correction_bounds hX hx
  have hp := abs_pow_sub_pow_le (a := Real.sqrt (Real.log X / Real.log x)) (b := (1 : ℝ)) k
  simp only [one_pow, abs_of_nonneg h0, abs_one, max_eq_right h1, one_pow, mul_one] at hp
  exact (hp.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg k))).trans_lt he

/-- Dyadic and fixed-scale moving increments differ by an explicit logarithmic and position factor. -/
theorem dyadicB_eq_movingB (E : ℝ → ℝ) (θ s X x : ℝ)
    (_hθ : 0 < θ) (_hθ1 : θ < 1) (hX : 1 < X) (hx : x ∈ Icc X (2 * X)) :
    dyadicB E θ s x = Real.sqrt (Real.log X / Real.log x) *
      dyadicU X x ^ (-θ / 2) * movingB E (fun u => s * u ^ θ) θ X x := by
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := hX0.trans_le hx.1
  have hu : 0 < x / X := div_pos hx0 hX0
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogx : 0 < Real.log x := Real.log_pos (hX.trans_le hx.1)
  have hscale : (x / X) ^ θ * X ^ θ = x ^ θ := by
    rw [Real.div_rpow hx0.le hX0.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hX0 θ).ne']
  have hpow : (x / X) ^ (-θ / 2) = (Real.sqrt ((x / X) ^ θ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le, ← Real.rpow_neg hu.le]
    congr 1
    ring
  have hsqrt : Real.sqrt ((x / X) ^ θ) * Real.sqrt (X ^ θ) = Real.sqrt (x ^ θ) := by
    rw [← Real.sqrt_mul (Real.rpow_nonneg hu.le _), hscale]
  dsimp [dyadicB, movingB, fixedScaleB, dyadicU]
  rw [mul_assoc s, hscale, hpow,
    Real.sqrt_div hlogX.le, Real.sqrt_mul (Real.rpow_nonneg hx0.le _),
    Real.sqrt_mul (Real.rpow_nonneg hX0.le _)]
  have hpX := Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hX0 θ)
  have hpx := Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hx0 θ)
  have hpU := Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hu θ)
  field_simp [hpX.ne', hpx.ne', hpU.ne', (Real.sqrt_pos.mpr hlogX).ne',
    (Real.sqrt_pos.mpr hlogx).ne']
  simpa only [mul_assoc] using
    congrArg (fun z : ℝ => increment E (s * x ^ θ) x * z) hsqrt


/-- Local fourth energy bounds all dyadic fourth moments uniformly in the length parameter. -/
theorem dyadic_fourth_uniform
    (E : ℝ → ℝ) (α θ β C : ℝ)
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : LocalFourthEnergyFor E α β C) :
    ∀ᶠ X : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E θ s x| ^ 4 ∂dyadicProbabilityMeasure X) ≤ fourthK C 2 := by
  have hθ : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    FourthMomentFreezing.moving_fourth_uniform hE hB hV
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)] with X hX hm
  intro s hs
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hb := hm (fun u => s * u ^ θ) (SecondOrderInterface.power_length_bounds hθ hθ1 hs)
  apply le_trans ?_ hb
  rw [dyadicProbabilityMeasure_integral hX0, dyadicProbabilityMeasure_integral hX0]
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  rw [intervalIntegral.integral_of_le hXX, intervalIntegral.integral_of_le hXX]
  have hi := VarianceTransfer.increment_pow_integrableOn (μ := volume)
    (K := Icc X (2 * X)) (u := fun x : ℝ => (s * (x / X) ^ θ) * X ^ θ)
    hE isCompact_Icc
    (continuous_const.mul ((Real.continuous_rpow_const hθ.le).comp
      (continuous_id.div_const X)) |>.mul continuous_const) continuous_id 4
  have hi' : IntegrableOn
      (fun x => |movingB E (fun u => s * u ^ θ) θ X x| ^ 4) (Icc X (2 * X)) := by
    simpa only [movingB, fixedScaleB, dyadicU, abs_div, div_pow, abs_pow, id_eq,
      IntegrableOn, Even.pow_abs (by decide : Even 4)] using
      hi.div_const (Real.sqrt (X ^ θ * Real.log X) ^ 4)
  have hiw := hi'.mul_continuousOn
    (continuousOn_id.inv₀ (fun x hx => (hX0.trans_le hx.1).ne')) isCompact_Icc
  apply integral_mono_of_nonneg
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact div_nonneg (by positivity) (hX0.trans hx.1).le)
    (by simpa only [div_eq_mul_inv, IntegrableOn, Pi.inv_apply, id_eq] using
      hiw.mono_set Ioc_subset_Icc_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hxc : x ∈ Icc X (2 * X) := ⟨hx.1.le, hx.2⟩
  have hu : 1 ≤ dyadicU X x := (le_div_iff₀ hX0).2 (by simpa using hxc.1)
  obtain ⟨hl0, hl1, _⟩ := logarithmic_correction_bounds hX hxc
  have hpow0 : 0 ≤ dyadicU X x ^ (-θ / 2) := Real.rpow_nonneg (by linarith) _
  have hpow1 : dyadicU X x ^ (-θ / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  apply div_le_div_of_nonneg_right _ (hX0.trans hx.1).le
  apply pow_le_pow_left₀ (abs_nonneg _) _ 4
  rw [dyadicB_eq_movingB E θ s X x hθ hθ1 (by linarith) hxc,
    abs_mul, abs_mul, abs_of_nonneg hl0, abs_of_nonneg hpow0]
  exact mul_le_of_le_one_left (abs_nonneg _)
    ((mul_le_mul_of_nonneg_right hl1 hpow0).trans (by simpa using hpow1))

private lemma weighted_product_normalization
    (E : ℝ → ℝ) (θ X x : ℝ) (k : ℕ) (s : Fin k → ℝ)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hX : 1 < X) (hx : x ∈ Icc X (2 * X)) :
    dyadicU X x ^ ((k : ℝ) * dyadicR θ) * (∏ i, dyadicB E θ (s i) x) =
      Real.sqrt (Real.log X / Real.log x) ^ k *
        (dyadicU X x ^ ((k : ℝ) * dyadicR θ - (k : ℝ) * θ / 2) *
          ∏ i, movingB E (fun u => s i * u ^ θ) θ X x) := by
  have hu : 0 < dyadicU X x := div_pos (by linarith [hx.1]) (by linarith)
  simp_rw [dyadicB_eq_movingB E θ _ X x hθ hθ1 hX hx]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow]
  rw [← Real.rpow_natCast (dyadicU X x ^ (-θ / 2)) k, ← Real.rpow_mul hu.le]
  rw [show (k : ℝ) * dyadicR θ - (k : ℝ) * θ / 2 =
    (k : ℝ) * dyadicR θ + (-θ / 2 * (k : ℝ)) by ring, Real.rpow_add hu]
  ring

/-- Interval-weighted fixed-scale moments with a homogeneous kernel give the dyadic moment interface. -/
theorem fixed_scale_dyadic_interface
    {E : ℝ → ℝ} {α θ β C : ℝ} {k : ℕ} {W : (Fin k → ℝ) → ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : LocalFourthEnergyFor E α β C) (hk : 0 < k) (hk4 : k ≤ 4)
    (hW : Continuous W) (hF : FixedScaleMixedMoments E θ k W)
    (hhom : ∀ (s : Fin k → ℝ), (∀ i, s i ∈ Icc (0 : ℝ) 1) →
      ∀ u ∈ Icc (1 : ℝ) 2,
        W (fun i => s i * u ^ θ) = u ^ ((k : ℝ) * θ / 2) * W s) :
    MomentInterface E θ k
      (fun s => DyadicMacroMoments.dyadicMacroMoment ((k : ℝ) * dyadicR θ) * W s) := by
  have hθ : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hK : 0 ≤ fourthK C 2 := by
    unfold fourthK
    exact div_nonneg (by positivity [hV.1]) (Real.log_pos (by norm_num)).le
  have hbound := dyadic_fourth_uniform E α θ β C hE hB hV
  refine ⟨⟨1 + fourthK C 2, by positivity, ?_⟩,
    (continuous_const.mul hW).measurable, ?_⟩
  · filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with X hb hX
    intro s hs
    let _ := dyadicProbabilityMeasure_isProbabilityMeasure (zero_lt_one.trans hX)
    have hi := (FirstOrderInterface.dyadicB_power_integrable (s := s) hE hθ.le hX 4).2
    have hi' : Integrable (fun x => 1 + |dyadicB E θ s x| ^ 4)
        (dyadicProbabilityMeasure X) := by
      apply ((integrable_const (1 : ℝ)).add hi).congr
      filter_upwards [] with x
      simp only [Pi.add_apply, Even.pow_abs (by decide : Even 4)]
    calc
      _ ≤ ∫ x, 1 + |dyadicB E θ s x| ^ 4 ∂dyadicProbabilityMeasure X := by
        apply integral_mono_of_nonneg (Eventually.of_forall (fun x => by positivity)) hi'
        exact Eventually.of_forall (fun x => by
          by_cases hx : |dyadicB E θ s x| ≤ 1
          · have hp := pow_le_one₀ (n := k) (abs_nonneg (dyadicB E θ s x)) hx
            linarith [pow_nonneg (abs_nonneg (dyadicB E θ s x)) 4]
          · have hp := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) hk4
            linarith)
      _ = 1 + ∫ x, |dyadicB E θ s x| ^ 4 ∂dyadicProbabilityMeasure X := by
        rw [integral_add (integrable_const _) (by
          simpa only [Even.pow_abs (by decide : Even 4)] using hi)]
        simp
      _ ≤ _ := add_le_add_right (hb s hs) 1
  intro s hs
  let b : Fin k → ℝ → ℝ := fun i u => s i * u ^ θ
  let γ : ℝ := (k : ℝ) * dyadicR θ - (k : ℝ) * θ / 2
  let w : ℝ → ℝ := fun u => u ^ γ
  have hw : ContinuousOn w (Icc (1 : ℝ) 2) :=
    continuousOn_id.rpow_const (fun u hu => Or.inl (by change u ≠ 0; linarith [hu.1]))
  have hb (i : Fin k) : MacroscopicLengthBounds (b i) 2 1 :=
    SecondOrderInterface.power_length_bounds hθ hθ1 (hs i)
  have hlim := FourthMomentMovingTransfer.moving_mixed_moments_tendsto
    hE hB hV hk hk4 hW hF b w (by norm_num) (by norm_num) hb hw
  have hlimit : (∫ u, w u * W (fun i => b i u) ∂dyadicProbabilityMeasure 1) =
      DyadicMacroMoments.dyadicMacroMoment ((k : ℝ) * dyadicR θ) * W s := by
    rw [DyadicMacroMoments.dyadicMacroMoment, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [MomentTransfer.ae_dyadic_mem 1] with u hu
    have hu' : u ∈ Icc (1 : ℝ) 2 := by simpa only [mul_one] using hu
    dsimp [b, w]
    rw [hhom s hs u hu', ← mul_assoc, ← Real.rpow_add (by linarith [hu'.1] : 0 < u)]
    congr 2
    dsimp [γ]
    ring
  rw [hlimit] at hlim
  have herror : Tendsto (fun X : ℝ => dyadicMixedMoment E θ X k s -
      ∫ x, w (dyadicU X x) * (∏ i, movingB E (b i) θ X x)
        ∂dyadicProbabilityMeasure X) atTop (𝓝 0) := by
    obtain ⟨B, hBbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
    let P := (fourthK C 2 ^ (1 / 4 : ℝ)) ^ k
    have hP : 0 ≤ P := by positivity
    have hPP : 0 < |B| * P + 1 := by positivity
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := ε / (|B| * P + 1)
    have hδ : 0 < δ := div_pos hε hPP
    filter_upwards [eventually_ge_atTop (4 : ℝ),
      logarithmic_correction_eventually k δ hδ,
      FourthMomentFreezing.moving_fourth_uniform hE hB hV
        (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1)] with X hX hlog hfourth
    have hX0 : 0 < X := by linarith
    let _ := dyadicProbabilityMeasure_isProbabilityMeasure hX0
    have hsupport := MomentTransfer.ae_dyadic_mem X
    have hpos (x : ℝ) (hx : x ∈ Icc X (2 * X)) : dyadicU X x ∈ Icc (1 : ℝ) 2 :=
      ⟨(le_div_iff₀ hX0).2 (by simpa using hx.1), (div_le_iff₀ hX0).2 hx.2⟩
    let A : Fin k → ℝ → ℝ := fun i => movingB E (b i) θ X
    have hA4 (i : Fin k) : MemLp (A i) 4 (dyadicProbabilityMeasure X) := by
      have hc : Continuous (fun x : ℝ => (s i * (x / X) ^ θ) * X ^ θ) :=
        (continuous_const.mul ((Real.continuous_rpow_const hθ.le).comp
          (continuous_id.div_const X))).mul continuous_const
      have hm : AEStronglyMeasurable (A i) (dyadicProbabilityMeasure X) := by
        dsimp [A, movingB, fixedScaleB, b, dyadicU, increment]
        exact (((hE.1.comp (continuous_id.add hc).measurable).sub hE.1).div_const _).aestronglyMeasurable
      have hi := VarianceTransfer.increment_pow_integrableOn (μ := dyadicProbabilityMeasure X)
        hE (K := Icc X (2 * X)) isCompact_Icc hc continuous_id 4
      rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hsupport] at hi
      apply (integrable_norm_rpow_iff hm (by norm_num : (4 : ℝ≥0∞) ≠ 0)
        (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
      simpa only [A, movingB, fixedScaleB, b, dyadicU, ENNReal.toReal_ofNat,
        Real.rpow_ofNat, Real.norm_eq_abs, abs_pow, Even.pow_abs (by decide : Even 4),
        div_pow, id_eq] using hi.div_const (Real.sqrt (X ^ θ * Real.log X) ^ 4)
    have hprodint : Integrable (fun x => ∏ i, A i x) (dyadicProbabilityMeasure X) :=
      FiniteProductMomentBounds.product_integrable hk
        (fun i => (hA4 i).mono_exponent (by exact_mod_cast hk4 : (k : ℝ≥0∞) ≤ 4))
    have hprodBound : (∫ x, |∏ i, A i x| ∂dyadicProbabilityMeasure X) ≤ P := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, P] using
        FiniteProductMomentBounds.product_fourth_bound hk hk4
          hA4 (fun _ => hK)
          (fun i => hfourth (b i) (hb i))
    have hwbound : ∀ᵐ x ∂dyadicProbabilityMeasure X, |w (dyadicU X x)| ≤ |B| := by
      filter_upwards [hsupport] with x hx
      have hbw : |w (dyadicU X x)| ≤ B := by
        simpa only [Real.norm_eq_abs] using hBbound _ (hpos x hx)
      exact hbw.trans (le_abs_self B)
    have hwi : Integrable (fun x => w (dyadicU X x) * ∏ i, A i x)
        (dyadicProbabilityMeasure X) := hprodint.bdd_mul (by
      dsimp [w, dyadicU]; exact ((measurable_id.div_const X).pow_const γ).aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using hwbound)
    have hli : Integrable (fun x => Real.sqrt (Real.log X / Real.log x) ^ k *
        (w (dyadicU X x) * ∏ i, A i x)) (dyadicProbabilityMeasure X) :=
      hwi.bdd_mul ((measurable_const.div measurable_id.log).sqrt.pow_const k).aestronglyMeasurable
      (c := (1 : ℝ)) (by
        filter_upwards [hsupport] with x hx
        obtain ⟨h0, h1, _⟩ := logarithmic_correction_bounds hX hx
        simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 k)] using
          pow_le_one₀ (n := k) h0 h1)
    have heq : dyadicMixedMoment E θ X k s =
        ∫ x, Real.sqrt (Real.log X / Real.log x) ^ k *
          (w (dyadicU X x) * ∏ i, A i x) ∂dyadicProbabilityMeasure X := by
      apply integral_congr_ae
      filter_upwards [hsupport] with x hx
      exact weighted_product_normalization E θ X x k s hθ hθ1 (by linarith) hx
    rw [Real.dist_eq, sub_zero, heq, ← integral_sub hli hwi]
    have he := norm_integral_le_of_norm_le
      (f := fun x => Real.sqrt (Real.log X / Real.log x) ^ k *
        (w (dyadicU X x) * ∏ i, A i x) - w (dyadicU X x) * ∏ i, A i x)
      (hprodint.abs.const_mul (δ * |B|)) (by
        filter_upwards [hsupport, hwbound] with x hx hwx
        change |Real.sqrt (Real.log X / Real.log x) ^ k *
          (w (dyadicU X x) * ∏ i, A i x) - w (dyadicU X x) * (∏ i, A i x)| ≤ _
        rw [← sub_one_mul, abs_mul, abs_mul]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul (hlog x hx).le hwx (abs_nonneg _) hδ.le)
          (abs_nonneg (∏ i, A i x)))
    rw [integral_const_mul] at he
    simp only [Real.norm_eq_abs] at he
    apply he.trans_lt
    apply (mul_le_mul_of_nonneg_left hprodBound (by positivity : 0 ≤ δ * |B|)).trans_lt
    have hcancel : δ * (|B| * P + 1) = ε := by dsimp [δ]; exact div_mul_cancel₀ _ hPP.ne'
    nlinarith
  simpa only [sub_add_cancel, zero_add] using herror.add hlim

end
end D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentDyadicTransfer
