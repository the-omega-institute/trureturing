/- GID: D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Different exponents have vanishing cross moments and strictly positive square correlation. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthMomentKurtosis
import D5.S3.Arith.Robin.ForwardKernel.CrossExponentOrthogonality
import D5.S3.Arith.Robin.ForwardKernel.JointBrownianKernel

namespace D5.S3.Arith.Robin.ForwardKernel.CrossExponentJointMoments

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs ProfileKernelDefs MomentTransferDefs DyadicProbability
open FourthMomentBandDefs FourthMomentInterfaceBridge
open MomentTransfer MomentTransferWeights CrossExponentOrthogonality
open FourthMomentKurtosis JointBrownianKernel BrownianFourthKernel DyadicMacroMoments MomentInterfaceBounds

noncomputable section
set_option autoImplicit false

private lemma jointZMoment_cross_eq
    {E g₁ g₂ : ℝ → ℝ} {a b X : ℝ} (hX : 1 < X) :
    jointZMoment E a b g₁ g₂ 1 1 X =
      ((∫ x in X..(2 * X), profileResponse E a g₁ x * profileResponse E b g₂ x / x) /
        (X ^ (1 - (a + b) / 2) * Real.log X)) / Real.log 2 := by
  rw [jointZMoment, dyadicProbabilityMeasure_integral (zero_lt_one.trans hX)]
  simp_rw [pow_one, dyadicZ, div_mul_div_comm]
  have hX0 : 0 < X := zero_lt_one.trans hX
  have ha : 0 ≤ meanSquareScale a X :=
    mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.log_nonneg hX.le)
  have hb : 0 ≤ meanSquareScale b X :=
    mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.log_nonneg hX.le)
  have hs : Real.sqrt (meanSquareScale a X) * Real.sqrt (meanSquareScale b X) =
      X ^ (1 - (a + b) / 2) * Real.log X := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.rpow_nonneg hX0.le _) (Real.log_nonneg hX.le))).mp
    have hp : (X ^ (1 - (a + b) / 2)) ^ 2 = X ^ ((1 - a) + (1 - b)) := by
      rw [← Real.rpow_mul_natCast hX0.le]
      congr 1
      ring
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, mul_pow, hp,
      Real.rpow_add hX0]
    dsimp [meanSquareScale]
    ring
  rw [hs]
  congr 1
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- The normalized first cross moment tends to zero under separated variance bands. -/
theorem jointZ_first_moment_tendsto_zero
    {E g₁ g₂ : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂)
    (hg₁ : ProfileIntegrable g₁) (hg₂ : ProfileIntegrable g₂) :
    Tendsto (jointZMoment E a b g₁ g₂ 1 1) atTop (𝓝 0) := by
  have hgap : 0 < min β₁ b - a := by
    exact sub_pos.mpr (lt_min hBa.2.2.1 hab)
  let μ := a + (min β₁ b - a) / 3
  let ν := a + 2 * (min β₁ b - a) / 3
  have haμ : a < μ := by dsimp [μ]; linarith
  have hμν : μ < ν := by dsimp [μ, ν]; linarith
  have hν : ν < min β₁ b := by dsimp [μ, ν]; linarith
  obtain ⟨C, hC, hbound⟩ := profile_cross_exponent_two_bands
    hE hBa hBb hab hVa hVb haμ hμν hν
  let d := min (μ - a) (min (ν - μ) (b - ν)) / 2
  have hd : 0 < d := by
    dsimp [d]
    have h1 : 0 < μ - a := sub_pos.mpr haμ
    have h2 : 0 < ν - μ := sub_pos.mpr hμν
    have h3 : 0 < b - ν := sub_pos.mpr (hν.trans_le (min_le_right _ _))
    exact div_pos (lt_min h1 (lt_min h2 h3)) (by norm_num)
  have hlim : Tendsto (fun X : ℝ => X ^ (-d)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hd
  apply (tendsto_zero_iff_norm_tendsto_zero).mpr
  refine squeeze_zero' (f := fun X : ℝ => ‖jointZMoment E a b g₁ g₂ 1 1 X‖)
    (g := fun X : ℝ => C * profileL1 g₁ * profileL1 g₂ / Real.log 2 * X ^ (-d)) ?_ ?_ ?_
  · filter_upwards [] with X
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (4 : ℝ), hbound] with X hX hEv
    have hX1 : 1 < X := by linarith
    rw [jointZMoment_cross_eq hX1]
    have h := hEv g₁ g₂ hg₁ hg₂
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hN : 0 < X ^ (1 - (a + b) / 2) * Real.log X := by
      have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
      positivity
    calc
      ‖((∫ x in X..(2 * X), profileResponse E a g₁ x * profileResponse E b g₂ x / x) /
          (X ^ (1 - (a + b) / 2) * Real.log X)) / Real.log 2‖ ≤
          (C * profileL1 g₁ * profileL1 g₂ *
            (X ^ (1 - (a + b) / 2) * Real.log X) * X ^ (-d) /
            (X ^ (1 - (a + b) / 2) * Real.log X)) / Real.log 2 := by
        rw [Real.norm_eq_abs, abs_div, abs_div, abs_of_pos hN, abs_of_pos hlog]
        apply div_le_div_of_nonneg_right _ (le_of_lt hlog)
        exact div_le_div_of_nonneg_right (by simpa [d] using h) (le_of_lt hN)
      _ = C * profileL1 g₁ * profileL1 g₂ / Real.log 2 * X ^ (-d) := by
        field_simp [hN.ne', hlog.ne', (Real.log_pos (by linarith : (1 : ℝ) < X)).ne']
  · simpa only [mul_zero] using
      hlim.const_mul (C * profileL1 g₁ * profileL1 g₂ / Real.log 2)

/-- The universal cross-kernel integral vanishes. -/
theorem cross_exponent_kernel_integral_zero
    {E : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ : ℝ} {M : (Fin 2 → ℝ) → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂)
    (hlim : ∀ s : Fin 2 → ℝ, (∀ i, s i ∈ Icc (0 : ℝ) 1) →
      Tendsto (fun X : ℝ => jointDyadicMixedMoment E ![a, b] X s) atTop (𝓝 (M s))) :
    ∀ g₁ g₂ : ℝ → ℝ, ProfileIntegrable g₁ → ProfileIntegrable g₂ →
      (∫ s : Fin 2 → ℝ, g₁ (s 0) * g₂ (s 1) * M s ∂cubeMeasure 2) = 0 := by
  intro g₁ g₂ hg₁ hg₂
  obtain ⟨C₁, hC₁, hb₁⟩ := second_moment_bound_interface hE hBa hVa
  obtain ⟨C₂, hC₂, hb₂⟩ := second_moment_bound_interface hE hBb hVb
  let e : Fin 2 → ℝ := ![a, b]
  let G : Fin 2 → ℝ → ℝ := ![g₁, g₂]
  have he0 : ∀ i, 0 < e i := by
    intro i
    fin_cases i
    · exact hBa.1.trans hBa.2.1
    · exact hBb.1.trans hBb.2.1
  have he1 : ∀ i, e i < 1 := by
    intro i
    fin_cases i
    · exact hBa.2.2.1.trans hBa.2.2.2
    · exact hBb.2.2.1.trans hBb.2.2.2
  have hG : ∀ i, ProfileIntegrable (G i) := by
    intro i
    fin_cases i <;> simp [G, hg₁, hg₂]
  let C := max C₁ C₂
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [le_max_left C₁ C₂, le_max_right C₁ C₂]
  have hb : ∀ i : Fin 2, ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
        (∫ x, |dyadicB E (e i) s x| ^ 2
          ∂dyadicProbabilityMeasure X) ≤ C := by
    intro i
    fin_cases i
    · filter_upwards [hb₁] with X hX s hs
      exact (hX s hs).trans (le_max_left _ _)
    · filter_upwards [hb₂] with X hX s hs
      exact (hX s hs).trans (le_max_right _ _)
  have hJ : JointMomentInterface E e (fun s => M s) := by
    refine ⟨⟨C, hC, ?_⟩, ?_⟩
    · filter_upwards [hb 0, hb 1] with X h0 h1 i s hs
      fin_cases i
      · exact h0 s hs
      · exact h1 s hs
    · intro s hs
      simpa [e] using hlim s hs
  have ht := joint_moment_transfer (e := e) (G := G) hE he0 he1 (by norm_num : 0 < 2) hG hJ
  have heq : jointZMoment E a b g₁ g₂ 1 1 =
      (fun X => ∫ x, dyadicZ E a g₁ X x * dyadicZ E b g₂ X x
        ∂dyadicProbabilityMeasure X) := by
    funext X
    simp [jointZMoment, Fin.prod_univ_two]
  have ht' : Tendsto (jointZMoment E a b g₁ g₂ 1 1) atTop
      (𝓝 (∫ s : Fin 2 → ℝ, g₁ (s 0) * g₂ (s 1) * M s ∂cubeMeasure 2)) := by
    rw [heq]
    simpa [e, G] using ht
  have hz := jointZ_first_moment_tendsto_zero hE hBa hBb hab hVa hVb hg₁ hg₂
  exact tendsto_nhds_unique ht' hz

/-- The separated-exponent mixed squares have strictly positive limiting covariance. -/
theorem cross_exponent_squares_positive_correlation
    {E g₁ g₂ : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ C₄₁ C₄₂ A : ℝ}
    {C : ℝ × ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂)
    (h₄a : FourthMomentBandBoundFor E α₁ β₁ C₄₁)
    (h₄b : FourthMomentBandBoundFor E α₂ β₂ C₄₂)
    (hg₁ : ProfileIntegrable g₁) (hg₂ : ProfileIntegrable g₂)
    (hC : Measurable C) (hA : 0 ≤ A)
    (hCb : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, |C (u, v)| ≤ A)
    (hI : JointBrownianFourthInterface E a b C) :
    Tendsto (jointZMoment E a b g₁ g₂ 1 1) atTop (𝓝 0) ∧
    Tendsto (jointZMoment E a b g₁ g₂ 2 2) atTop
      (𝓝 (dyadicMacroMoment (kappa a + kappa b) * kappa a * kappa b * Q g₁ * Q g₂)) ∧
    Tendsto (fun X : ℝ => jointZMoment E a b g₁ g₂ 2 2 X -
      (∫ x, dyadicZ E a g₁ X x ^ 2 ∂dyadicProbabilityMeasure X) *
      (∫ x, dyadicZ E b g₂ X x ^ 2 ∂dyadicProbabilityMeasure X)) atTop
      (𝓝 (kappa a * kappa b * Q g₁ * Q g₂ *
        (dyadicMacroMoment (kappa a + kappa b) -
          dyadicMacroMoment (kappa a) * dyadicMacroMoment (kappa b)))) ∧
    dyadicMacroMoment (kappa a) * dyadicMacroMoment (kappa b) <
      dyadicMacroMoment (kappa a + kappa b) ∧
    ((¬ (g₁ =ᵐ[unitMeasure] 0)) → (¬ (g₂ =ᵐ[unitMeasure] 0)) →
      0 < kappa a * kappa b * Q g₁ * Q g₂ *
        (dyadicMacroMoment (kappa a + kappa b) -
          dyadicMacroMoment (kappa a) * dyadicMacroMoment (kappa b))) := by
  have hfirst := jointZ_first_moment_tendsto_zero hE hBa hBb hab hVa hVb hg₁ hg₂
  have hka : 0 < kappa a := sub_pos.mpr (hBa.2.2.1.trans hBa.2.2.2)
  have hkb : 0 < kappa b := sub_pos.mpr (hBb.2.2.1.trans hBb.2.2.2)
  have hsum : 0 < kappa a + kappa b := add_pos hka hkb
  obtain ⟨C₄a, hC₄a, hb₄a⟩ := fourth_moment_bound_interface hE hBa h₄a
  obtain ⟨C₄b, hC₄b, hb₄b⟩ := fourth_moment_bound_interface hE hBb h₄b
  let e : Fin 4 → ℝ := ![a, a, b, b]
  let G : Fin 4 → ℝ → ℝ := ![g₁, g₁, g₂, g₂]
  let C₄ := max C₄a C₄b
  have hC₄ : 0 ≤ C₄ := by
    dsimp [C₄]
    linarith [le_max_left C₄a C₄b, le_max_right C₄a C₄b]
  have he0 : ∀ i, 0 < e i := by
    intro i
    fin_cases i <;> simp [e, hBa.1.trans hBa.2.1, hBb.1.trans hBb.2.1]
  have he1 : ∀ i, e i < 1 := by
    intro i
    fin_cases i <;> simp [e, hBa.2.2.1.trans hBa.2.2.2, hBb.2.2.1.trans hBb.2.2.2]
  have hG : ∀ i, ProfileIntegrable (G i) := by
    intro i
    fin_cases i <;> simp [G, hg₁, hg₂]
  have hb : ∀ i : Fin 4, ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
        (∫ x, |dyadicB E (e i) s x| ^ 4
          ∂dyadicProbabilityMeasure X) ≤ C₄ := by
    intro i
    fin_cases i
    · filter_upwards [hb₄a] with X hX s hs
      exact (hX s hs).trans (le_max_left _ _)
    · filter_upwards [hb₄a] with X hX s hs
      exact (hX s hs).trans (le_max_left _ _)
    · filter_upwards [hb₄b] with X hX s hs
      exact (hX s hs).trans (le_max_right _ _)
    · filter_upwards [hb₄b] with X hX s hs
      exact (hX s hs).trans (le_max_right _ _)
  have hJ4 : JointMomentInterface E e (fun s =>
      dyadicMacroMoment (kappa a + kappa b) * brownianW22 (kappa a) (kappa b) C s) := by
    refine ⟨⟨C₄, hC₄, ?_⟩, ?_⟩
    · filter_upwards [hb 0, hb 1, hb 2, hb 3] with X h0 h1 h2 h3 i s hs
      fin_cases i
      · exact h0 s hs
      · exact h1 s hs
      · exact h2 s hs
      · exact h3 s hs
    · intro s hs
      simpa [e] using hI.2 s hs
  have ht4 := joint_moment_transfer (e := e) (G := G) hE he0 he1
    (by norm_num : 0 < 4) hG hJ4
  have heq4 : jointZMoment E a b g₁ g₂ 2 2 =
      (fun X => ∫ x, dyadicZ E a g₁ X x ^ 2 * dyadicZ E b g₂ X x ^ 2
        ∂dyadicProbabilityMeasure X) := by
    funext X
    simp [jointZMoment]
  have hcrosslim : Tendsto (jointZMoment E a b g₁ g₂ 2 2) atTop
      (𝓝 (∫ s : Fin 4 → ℝ, (∏ i, G i (s i)) *
        (dyadicMacroMoment (kappa a + kappa b) *
          brownianW22 (kappa a) (kappa b) C s) ∂cubeMeasure 4)) := by
    rw [heq4]
    convert ht4 using 1 <;> simp [pow_two, e, G, Fin.prod_univ_four] <;> ring
  have hcross_eq :
      (∫ s : Fin 2 → ℝ, g₁ (s 0) * g₂ (s 1) * C (s 0, s 1)
        ∂cubeMeasure 2) = crossKernelForm g₁ g₂ C := by
    exact (measurePreserving_finTwoArrow unitMeasure).integral_comp'
      (fun z : ℝ × ℝ => g₁ z.1 * g₂ z.2 * C z)
  have hcross_zero : crossKernelForm g₁ g₂ C = 0 := by
    have hz := cross_exponent_kernel_integral_zero hE hBa hBb hab hVa hVb
      (M := fun s : Fin 2 → ℝ => dyadicMacroMoment (dyadicR a + dyadicR b) * C (s 0, s 1))
      hI.1 g₁ g₂ hg₁ hg₂
    have hm : 0 < dyadicMacroMoment (dyadicR a + dyadicR b) :=
      dyadic_macro_moment_pos (by dsimp [dyadicR]; positivity)
    have hz' : dyadicMacroMoment (dyadicR a + dyadicR b) *
        (∫ s : Fin 2 → ℝ, g₁ (s 0) * g₂ (s 1) * C (s 0, s 1)
          ∂cubeMeasure 2) = 0 := by
      calc
        _ = ∫ s : Fin 2 → ℝ, dyadicMacroMoment (dyadicR a + dyadicR b) *
              (g₁ (s 0) * g₂ (s 1) * C (s 0, s 1)) ∂cubeMeasure 2 := by
                rw [integral_const_mul]
        _ = ∫ s : Fin 2 → ℝ, g₁ (s 0) * g₂ (s 1) *
            (dyadicMacroMoment (dyadicR a + dyadicR b) * C (s 0, s 1))
              ∂cubeMeasure 2 := by
                apply integral_congr_ae
                filter_upwards [] with s
                ring
        _ = 0 := hz
    rw [hcross_eq] at hz'
    exact (mul_eq_zero.mp hz').resolve_left (ne_of_gt hm)
  have hEval :
      (∫ s : Fin 4 → ℝ, (∏ i, G i (s i)) *
        (dyadicMacroMoment (kappa a + kappa b) *
          brownianW22 (kappa a) (kappa b) C s) ∂cubeMeasure 4) =
        dyadicMacroMoment (kappa a + kappa b) * kappa a * kappa b * Q g₁ * Q g₂ := by
    have hprod (s : Fin 4 → ℝ) : (∏ i, G i (s i)) =
        g₁ (s 0) * g₁ (s 1) * g₂ (s 2) * g₂ (s 3) := by
      simp [G, Fin.prod_univ_four]
    simp_rw [hprod]
    simp_rw [show ∀ s : Fin 4 → ℝ,
      (g₁ (s 0) * g₁ (s 1) * g₂ (s 2) * g₂ (s 3)) *
          (dyadicMacroMoment (kappa a + kappa b) * brownianW22 (kappa a) (kappa b) C s) =
        dyadicMacroMoment (kappa a + kappa b) *
          ((g₁ (s 0) * g₁ (s 1) * g₂ (s 2) * g₂ (s 3)) *
            brownianW22 (kappa a) (kappa b) C s) from fun s => by ring]
    rw [integral_const_mul, brownianW22_integral hg₁ hg₂ hC hA hCb, hcross_zero]
    ring
  have hfour : Tendsto (jointZMoment E a b g₁ g₂ 2 2) atTop
      (𝓝 (dyadicMacroMoment (kappa a + kappa b) * kappa a * kappa b * Q g₁ * Q g₂)) := by
    rw [hEval] at hcrosslim
    exact hcrosslim
  have hma : dyadicMacroMoment (kappa a) * kappa a * Q g₁ =
      (2 ^ kappa a - 1) * Q g₁ / Real.log 2 := by
    rw [dyadic_macro_moment_eq hka]
    field_simp [hka.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hmb : dyadicMacroMoment (kappa b) * kappa b * Q g₂ =
      (2 ^ kappa b - 1) * Q g₂ / Real.log 2 := by
    rw [dyadic_macro_moment_eq hkb]
    field_simp [hkb.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hseconda := dyadicZ_second_moment_tendsto hE hBa hVa hg₁
  have hsecondb := dyadicZ_second_moment_tendsto hE hBb hVb hg₂
  have hseconda' : Tendsto (fun X : ℝ =>
      ∫ x, dyadicZ E a g₁ X x ^ 2 ∂dyadicProbabilityMeasure X) atTop
      (𝓝 (dyadicMacroMoment (kappa a) * kappa a * Q g₁)) := by
    rw [hma]
    exact hseconda
  have hsecondb' : Tendsto (fun X : ℝ =>
      ∫ x, dyadicZ E b g₂ X x ^ 2 ∂dyadicProbabilityMeasure X) atTop
      (𝓝 (dyadicMacroMoment (kappa b) * kappa b * Q g₂)) := by
    rw [hmb]
    exact hsecondb
  have hcov := hfour.sub (hseconda'.mul hsecondb')
  have hstrict := dyadic_macro_moment_strict_mul hka hkb
  refine ⟨hfirst, hfour, ?_, hstrict, ?_⟩
  · convert hcov using 1 <;> ring
  · intro hg₁ne hg₂ne
    have hQ₁ : 0 < Q g₁ := (ProfileQuadraticForm.Q_pos_iff hg₁).mpr hg₁ne
    have hQ₂ : 0 < Q g₂ := (ProfileQuadraticForm.Q_pos_iff hg₂).mpr hg₂ne
    have hdiff : 0 < dyadicMacroMoment (kappa a + kappa b) -
        dyadicMacroMoment (kappa a) * dyadicMacroMoment (kappa b) :=
      sub_pos.mpr hstrict
    positivity

end
end D5.S3.Arith.Robin.ForwardKernel.CrossExponentJointMoments
