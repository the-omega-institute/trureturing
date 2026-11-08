/- GID: D5/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CrossExponentJointMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Different exponents have vanishing cross moments and strictly positive square correlation. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthMomentKurtosis
import D5.S3.Arith.Robin.ForwardKernel.CrossOrderInterface
import D5.S3.Arith.Robin.ForwardKernel.JointBrownianKernel

namespace D5.S3.Arith.Robin.ForwardKernel.CrossExponentJointMoments

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs ProfileKernelDefs MomentTransferDefs DyadicProbability
open FourthMomentBandDefs FourthMomentInterfaceBridge
open MomentTransfer MomentTransferWeights
open FourthMomentKurtosis JointBrownianKernel BrownianFourthKernel DyadicMacroMoments MomentInterfaceBounds

noncomputable section
set_option autoImplicit false

/-- The normalized first cross moment tends to zero under separated variance bands. -/
theorem jointZ_first_moment_tendsto_zero
    {E g₁ g₂ : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂) (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂)
    (hg₁ : ProfileIntegrable g₁) (hg₂ : ProfileIntegrable g₂) :
    Tendsto (jointZMoment E a b g₁ g₂ 1 1) atTop (𝓝 0) := by
  have he0 : ∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · exact hBa.1.trans hBa.2.1
    · exact hBb.1.trans hBb.2.1
  have he1 : ∀ i : Fin 2, (![a, b] : Fin 2 → ℝ) i < 1 := by
    intro i
    fin_cases i
    · exact hBa.2.2.1.trans hBa.2.2.2
    · exact hBb.2.2.1.trans hBb.2.2.2
  have hG : ∀ i : Fin 2, ProfileIntegrable ((![g₁, g₂] : Fin 2 → ℝ → ℝ) i) := by
    intro i
    fin_cases i
    · exact hg₁
    · exact hg₂
  change Tendsto (fun X => jointZMoment E a b g₁ g₂ 1 1 X) atTop (𝓝 0)
  simpa only [jointZMoment, pow_one, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, integral_zero] using
    joint_moment_transfer (G := ![g₁, g₂]) hE he0 he1 (by norm_num : 0 < 2) hG
      (CrossOrderInterface.cross_moment_interface hE hBa hBb hab hVa hVb)

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
  have hJ : JointMomentInterface E ![a, b] M :=
    ⟨(CrossOrderInterface.cross_moment_interface hE hBa hBb hab hVa hVb).1, hlim⟩
  have he0 : ∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · exact hBa.1.trans hBa.2.1
    · exact hBb.1.trans hBb.2.1
  have he1 : ∀ i : Fin 2, (![a, b] : Fin 2 → ℝ) i < 1 := by
    intro i
    fin_cases i
    · exact hBa.2.2.1.trans hBa.2.2.2
    · exact hBb.2.2.1.trans hBb.2.2.2
  have hG : ∀ i : Fin 2, ProfileIntegrable ((![g₁, g₂] : Fin 2 → ℝ → ℝ) i) := by
    intro i
    fin_cases i
    · exact hg₁
    · exact hg₂
  have ht := joint_moment_transfer (G := ![g₁, g₂]) hE he0 he1
    (by norm_num : 0 < 2) hG hJ
  have ht' : Tendsto (jointZMoment E a b g₁ g₂ 1 1) atTop
      (𝓝 (∫ s : Fin 2 → ℝ, g₁ (s 0) * g₂ (s 1) * M s ∂cubeMeasure 2)) := by
    change Tendsto (fun X => jointZMoment E a b g₁ g₂ 1 1 X) atTop _
    simpa only [jointZMoment, pow_one, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] using ht
  exact tendsto_nhds_unique ht'
    (jointZ_first_moment_tendsto_zero hE hBa hBb hab hVa hVb hg₁ hg₂)

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
