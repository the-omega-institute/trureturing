/- GID: D5/S3/Arith/Robin/ForwardKernel/CrossOrderInterface
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CrossOrderInterface
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separate variance bands give uniform continuously weighted cross-moment cancellation. -/

import D5.S3.Arith.Robin.ForwardKernel.FirstOrderInterface

/-! Uniform cross moments on dyadic subintervals and with continuous macroscopic weights. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CrossOrderInterface

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer CrossExponentDefs MomentTransferDefs
open DyadicProbability MacroscopicVarianceDefs FirstOrderInterface

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Intermediate variance scales make all cross integrals negligible uniformly in
both moving-length parameters and all dyadic subintervals. -/
theorem cross_interval_cancellation {E : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ A ∈ Icc X (2 * X), ∀ B ∈ Icc A (2 * X),
        |∫ x in A..B, movingIncrement E a s x * movingIncrement E b t x| <
          ε * (X ^ (1 + (a + b) / 2) * Real.log X) := by
  obtain ⟨μ, haμ, hμ⟩ := exists_between (lt_min hBa.2.2.1 hab)
  obtain ⟨ν, hμν, hν⟩ := exists_between hμ
  have hBμ : ValidBand α₁ μ β₁ :=
    ⟨hBa.1, hBa.2.1.trans haμ, hμ.trans_le (min_le_left _ _), hBa.2.2.2⟩
  have hBν : ValidBand α₁ ν β₁ :=
    ⟨hBa.1, hBa.2.1.trans (haμ.trans hμν), hν.trans_le (min_le_left _ _), hBa.2.2.2⟩
  have hνb : ν < b := hν.trans_le (min_le_right _ _)
  have hr (p q : ℝ) (hpq : p < q) :
      Tendsto (fun X : ℝ => X ^ p / X ^ q) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (sub_pos.mpr hpq)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [neg_sub, Real.rpow_sub hX]
  have ho (p q : ℝ) (hpq : p < q) :
      Asymptotics.IsBigO atTop (fun X : ℝ => X ^ p) (fun X => X ^ q) := by
    apply Asymptotics.isBigO_of_div_tendsto_nhds _ 0 (hr p q hpq)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX hz
    exact ((Real.rpow_pos_of_pos hX q).ne' hz).elim
  obtain ⟨C, hC, hc⟩ := FourScaleCovariance.four_scale_covariance_bound
    hE (hBa.1.trans hBa.2.1) hab (hBb.2.2.1.trans hBb.2.2.2)
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBa hVa)
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBμ hVa)
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBν hVa)
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBb hVb)
    (ho a μ haμ) (ho μ ν hμν) (ho ν b hνb)
  have ht : Tendsto (fun X : ℝ => C *
      (Real.sqrt (X ^ a / X ^ μ) + Real.sqrt (X ^ μ / X ^ ν) +
        Real.sqrt (X ^ ν / X ^ b))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, add_zero, mul_zero] using
      (tendsto_const_nhds (x := C)).mul
        (((hr a μ haμ).sqrt.add (hr μ ν hμν).sqrt).add (hr ν b hνb).sqrt)
  intro ε hε
  filter_upwards [hc, ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)]
    with X hc ht hX s hs t ht' A hA B hB
  have hX0 : 0 < X := zero_lt_one.trans hX
  have he : (X * Real.log X) * Real.sqrt (X ^ a * X ^ b) =
      X ^ (1 + (a + b) / 2) * Real.log X := by
    rw [← Real.rpow_add hX0, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le,
      Real.rpow_add hX0, Real.rpow_one]
    simp only [div_eq_mul_inv]
    ring
  calc
    _ ≤ C * (X * Real.log X) * Real.sqrt (X ^ a * X ^ b) *
        (Real.sqrt (X ^ a / X ^ μ) + Real.sqrt (X ^ μ / X ^ ν) +
          Real.sqrt (X ^ ν / X ^ b)) := hc s hs t ht' A hA B hB
    _ = (C * (Real.sqrt (X ^ a / X ^ μ) + Real.sqrt (X ^ μ / X ^ ν) +
          Real.sqrt (X ^ ν / X ^ b))) *
        (X ^ (1 + (a + b) / 2) * Real.log X) := by rw [← he]; ring
    _ < _ := mul_lt_mul_of_pos_right ht (mul_pos (Real.rpow_pos_of_pos hX0 _)
      (Real.log_pos hX))

private lemma cross_weight_eq {E : ℝ → ℝ} {a b s t x : ℝ} (hx : 1 < x) :
    dyadicB E a s x * dyadicB E b t x / x =
      (1 / (x ^ (1 + (a + b) / 2) * Real.log x)) *
        (movingIncrement E a s x * movingIncrement E b t x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have he : Real.sqrt (x ^ a * Real.log x) * Real.sqrt (x ^ b * Real.log x) * x =
      x ^ (1 + (a + b) / 2) * Real.log x := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hx0.le _),
      Real.sqrt_mul (Real.rpow_nonneg hx0.le _), Real.sqrt_eq_rpow (x := x ^ a),
      Real.sqrt_eq_rpow (x := x ^ b), ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    have hsq := Real.mul_self_sqrt (Real.log_pos hx).le
    rw [Real.rpow_add hx0, Real.rpow_one]
    have hp : x ^ (a * (1 / 2)) * x ^ (b * (1 / 2)) = x ^ ((a + b) / 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    calc
      _ = (x ^ (a * (1 / 2)) * x ^ (b * (1 / 2))) *
          (Real.sqrt (Real.log x) * Real.sqrt (Real.log x)) * x := by ring
      _ = _ := by rw [hp, hsq]; ring
  simp only [dyadicB, movingIncrement, div_mul_div_comm, div_div]
  rw [he]
  ring

/-- Cross moments cancel uniformly on every dyadic subinterval after logarithmic normalization. -/
theorem cross_weighted_interval_cancellation {E : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ A ∈ Icc X (2 * X), ∀ B ∈ Icc A (2 * X),
        |∫ x in A..B, dyadicB E a s x * dyadicB E b t x / x| < ε := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := hBb.1.trans hBb.2.1
  have hh := logarithmic_weight_cancellation
    (f := fun _ (st : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) x =>
      movingIncrement E a st.1 x * movingIncrement E b st.2 x)
    (p := 1 + (a + b) / 2) (q := 1) (by positivity) zero_le_one
    (by
      intro X hX st A B
      exact (increment_product_comp_integrableOn hE isCompact_uIcc
        (continuous_const.mul (Real.continuous_rpow_const ha.le)) continuous_id
        (continuous_const.mul (Real.continuous_rpow_const hb.le)) continuous_id).intervalIntegrable)
    (by
      intro ε hε
      filter_upwards [cross_interval_cancellation hE hBa hBb hab hVa hVb ε hε]
        with X hx st A hA B hB
      simpa only [Real.rpow_one] using hx st.1 st.1.property st.2 st.2.property A hA B hB)
  intro ε hε
  filter_upwards [hh ε hε, eventually_gt_atTop (1 : ℝ)] with X hh hX
  intro s hs t ht A hA B hB
  have he : (∫ x in A..B, dyadicB E a s x * dyadicB E b t x / x) =
      ∫ x in A..B, (1 / (x ^ (1 + (a + b) / 2) * (Real.log x) ^ (1 : ℝ))) *
        (movingIncrement E a s x * movingIncrement E b t x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hB.1] at hx
    simpa only [Real.rpow_one] using cross_weight_eq (E := E) (a := a) (b := b)
      (s := s) (t := t) (hX.trans_le (hA.1.trans hx.1))
  rw [he]
  exact hh (⟨s, hs⟩, ⟨t, ht⟩) A hA B hB

private lemma cross_integrable {E : ℝ → ℝ} {a b s t X : ℝ}
    (hE : LocallyBoundedMeasurable E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : 1 < X) :
    IntervalIntegrable (fun x => dyadicB E a s x * dyadicB E b t x / x)
      volume X (2 * X) := by
  have hr := (increment_product_comp_integrableOn (μ := volume) hE
    (K := uIcc X (2 * X))
    (u := fun x => s * x ^ a) (v := fun x => t * x ^ b) isCompact_uIcc
    (continuous_const.mul (Real.continuous_rpow_const ha)) continuous_id
    (continuous_const.mul (Real.continuous_rpow_const hb)) continuous_id).intervalIntegrable
  have hw := (logarithmic_weight_regular (p := 1 + (a + b) / 2) (q := 1)
    (by positivity) zero_le_one).1.continuousOn
  have hi := hr.continuousOn_mul (hw.mono (show uIcc X (2 * X) ⊆ Ioi (1 : ℝ) from by
    intro x hx
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
    exact hX.trans_le hx.1))
  apply hi.congr
  intro x hx
  rw [uIoc_of_le (by linarith : X ≤ 2 * X)] at hx
  simpa only [Real.rpow_one, mul_comm, id_eq, movingIncrement] using
    (cross_weight_eq (E := E) (a := a) (b := b) (s := s) (t := t)
      (hX.trans_le hx.1.le)).symm

/-- Separate variance bands force continuously weighted cross moments to vanish uniformly. -/
theorem cross_moment_uniform {E : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (1 : ℝ) 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |weightedDyadicCovariance E φ a b X s t| < ε := by
  have ha : 0 ≤ a := (hBa.1.trans hBa.2.1).le
  have hb : 0 ≤ b := (hBb.1.trans hBb.2.1).le
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Ca, hCa, hca⟩ := MomentInterfaceBounds.second_moment_bound_interface hE hBa hVa
  obtain ⟨Cb, hCb, hcb⟩ := MomentInterfaceBounds.second_moment_bound_interface hE hBb hVb
  have hh := continuous_dyadic_weight_lifting
    (g := fun _ (st : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1) x =>
      dyadicB E a st.1 x * dyadicB E b st.2 x)
    (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX st
      exact cross_integrable hE ha hb hX)
    (by
      refine ⟨(Ca + Cb) * Real.log 2, mul_nonneg (add_nonneg hCa hCb) hl.le, ?_⟩
      filter_upwards [hca, hcb, eventually_gt_atTop (1 : ℝ)] with X hca hcb hX st
      have hX0 : 0 < X := zero_lt_one.trans hX
      have hi₁ := (dyadicB_power_integrable (s := st.1) hE ha hX 2).1
      have hi₂ := (dyadicB_power_integrable (s := st.2) hE hb hX 2).1
      have h₁ : (∫ x in X..(2 * X), dyadicB E a st.1 x ^ 2 / x) ≤ Ca * Real.log 2 := by
        have h := hca st.1 st.1.property
        simp only [sq_abs] at h
        rw [dyadicProbabilityMeasure_integral hX0] at h
        exact (div_le_iff₀ hl).mp h
      have h₂ : (∫ x in X..(2 * X), dyadicB E b st.2 x ^ 2 / x) ≤ Cb * Real.log 2 := by
        have h := hcb st.2 st.2.property
        simp only [sq_abs] at h
        rw [dyadicProbabilityMeasure_integral hX0] at h
        exact (div_le_iff₀ hl).mp h
      calc
        _ ≤ ∫ x in X..(2 * X),
            dyadicB E a st.1 x ^ 2 / x + dyadicB E b st.2 x ^ 2 / x := by
          apply intervalIntegral.integral_mono_on (by linarith)
            (cross_integrable hE ha hb hX).abs (hi₁.add hi₂)
          intro x hx
          have hx0 : 0 < x := hX0.trans_le hx.1
          rw [abs_div, abs_mul, abs_of_pos hx0, ← add_div]
          apply div_le_div_of_nonneg_right _ hx0.le
          nlinarith [sq_nonneg (|dyadicB E a st.1 x| - |dyadicB E b st.2 x|),
            sq_abs (dyadicB E a st.1 x), sq_abs (dyadicB E b st.2 x)]
        _ = (∫ x in X..(2 * X), dyadicB E a st.1 x ^ 2 / x) +
            ∫ x in X..(2 * X), dyadicB E b st.2 x ^ 2 / x :=
          intervalIntegral.integral_add hi₁ hi₂
        _ ≤ _ := by nlinarith)
    (by
      intro ε hε
      filter_upwards [cross_weighted_interval_cancellation hE hBa hBb hab hVa hVb ε hε]
        with X hX st
      exact hX st.1 st.1.property st.2 st.2.property) hφ
  intro ε hε
  filter_upwards [hh ε hε] with X hh s hs t ht
  simpa only [weightedDyadicCovariance, mul_assoc] using hh (⟨s, hs⟩, ⟨t, ht⟩)

/-- Separate variance bands supply the two second-moment bounds and the zero cross kernel. -/
theorem cross_moment_interface {E : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂) :
    JointMomentInterface E ![a, b] (fun _ => 0) := by
  obtain ⟨Ca, hCa, hca⟩ := MomentInterfaceBounds.second_moment_bound_interface hE hBa hVa
  obtain ⟨Cb, hCb, hcb⟩ := MomentInterfaceBounds.second_moment_bound_interface hE hBb hVb
  refine ⟨⟨max Ca Cb, hCa.trans (le_max_left _ _), ?_⟩, ?_⟩
  · filter_upwards [hca, hcb] with X hca hcb i s hs
    fin_cases i
    · exact (hca s hs).trans (le_max_left _ _)
    · exact (hcb s hs).trans (le_max_right _ _)
  · intro s hs
    have hw := cross_moment_uniform hE hBa hBb hab hVa hVb
      (φ := fun u : ℝ => u ^ (dyadicR a + dyadicR b))
      (continuousOn_id.rpow_const (fun u hu => Or.inl (by
        change u ≠ 0
        linarith [hu.1])))
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hw ε hε] with X hX
    simpa only [Real.dist_eq, sub_zero, jointDyadicMixedMoment, weightedDyadicCovariance,
      Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_assoc] using hX (s 0) (hs 0) (s 1) (hs 1)

end
end D5.S3.Arith.Robin.ForwardKernel.CrossOrderInterface
