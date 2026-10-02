/- GID: D5/S3/Weil/PrimeNumberTheorem/PntContourBound
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeNumberTheorem/PntContourBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contour deformation controls the smoothed Chebyshev reading. -/

/-
Source: AlexKontorovich/PrimeNumberTheoremAnd, revision 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.
Original file: PrimeNumberTheoremAnd/MediumPNT.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Full license and upstream attribution: Library/Weil/primenumbertheoremand2026medium.md.
This file is modified from the cited source.
Retirement: replace this consumed closure with direct references when this
repository's adopted Mathlib revision contains equivalent quantified contracts.
-/

import D5.S3.Weil.PrimeNumberTheorem.PntShortContour

set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory ComplexConjugate Topology
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin
local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

set_option maxHeartbeats 800000 in
/-- The contour deformation and its short vertical estimate for the same smoothed integrand. -/
theorem SmoothedChebyshevContourBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    {σ₂ : ℝ} (holoSmall : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1) :
    ∃ C₅ > 0, ∀ (X ε T σ₁ : ℝ), 3 < X → 0 < ε → ε < 1 → 3 < T →
      0 < σ₁ → σ₁ < 1 → σ₂ < σ₁ →
      HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2 ×ℂ Icc (-T) T) \ {1}) →
      HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
        (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) →
      ‖SmoothedChebyshev SmoothingF ε X -
          𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X‖ ≤
        ‖I₁ SmoothingF ε X T‖ + ‖I₂ SmoothingF ε T X σ₁‖ +
        ‖I₃ SmoothingF ε T X σ₁‖ + ‖I₄ SmoothingF ε X σ₁ σ₂‖ +
        C₅ * X ^ σ₂ / ε + ‖I₆ SmoothingF ε X σ₁ σ₂‖ +
        ‖I₇ SmoothingF ε T X σ₁‖ + ‖I₈ SmoothingF ε T X σ₁‖ +
        ‖I₉ SmoothingF ε X T‖ := by
  have Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
      (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
      Smooth1 ν ε x ≤ 1 := by
    have hSym {𝕂 : Type} [RCLike 𝕂] (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
        MellinConvolution f g x = MellinConvolution g f x := by
      have hMul (h : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
          ∫ y in Ioi 0, h (y * a) / y = ∫ y in Ioi 0, h y / y := by
        have hh := integral_comp_mul_right_Ioi (fun y ↦ h y / y) 0 ha
        simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at hh
        rw [← integral_smul] at hh
        rw [← hh, setIntegral_congr_fun (by simp)]
        intro _ _
        simp only [RCLike.real_smul_eq_coe_mul]
        rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
        exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha
      have hInv (h : ℝ → 𝕂) :
          ∫ y in Ioi 0, h (1 / y) / y = ∫ y in Ioi 0, h y / y := by
        have hh := integral_comp_rpow_Ioi (fun y ↦ h y / y) (p := -1) (by simp)
        rw [← hh, setIntegral_congr_fun (by simp)]
        intro y hy
        have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
        simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
          RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
        ring_nf
        simp [field]
      unfold MellinConvolution
      calc
        _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
        _ = _ := ?_
      · rw [← hMul (fun y ↦ f y * g (x / y)) xpos]
        simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
      · convert (hInv fun y ↦ f (y * x) * g (1 / y)).symm using 3
        rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]
    have hDiv (h : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
        ∫ y in Ioi 0, h (a / y) / y = ∫ y in Ioi 0, h y / y := by
      simpa only [MellinConvolution, one_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq] using
        (hSym (𝕂 := ℝ) (fun _ : ℝ ↦ (1 : ℝ)) h ha)
    have hPow (h : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
        ∫ y in Ioi 0, |p| * h (y ^ p) / y = ∫ y in Ioi 0, h y / y := by
      rw [← integral_comp_rpow_Ioi (fun y ↦ h y / y) hp,
        setIntegral_congr_fun (by simp)]
      intro y hy
      have ypos : 0 < y := mem_Ioi.mp hy
      simp only [rpow_sub_one ypos.ne', smul_eq_mul]
      field_simp
    have hMass : ∫ y in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
      calc
        _ = ∫ y in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
        _ = ∫ y in Ioi 0, ν y / y := ?_
        _ = 1 := mass_one
      · have hh := hDiv (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
        convert! hh.symm using 1
        congr; funext y; congr; field_simp [mul_comm]
      · have hh := hPow (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
        rw [← hh, abs_of_pos <| one_div_pos.mpr εpos]
        field_simp
    unfold Smooth1 MellinConvolution DeltaSpike
    calc
      _ = ∫ (y : ℝ) in Ioi 0,
          (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
      _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
      _ = 1 := hMass
    · rw [setIntegral_congr_fun (by simp)]
      simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
      intro y hy; aesop
    · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one hMass) (by simp) ?_
      · refine integrable_of_integral_eq_one hMass |>.bdd_mul ?_
          (ae_of_all _ <| by aesop)
        have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) =
            indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
          aesop
        simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
        exact aestronglyMeasurable_one
      · simp only [ite_mul, one_mul, zero_mul]
        intro y hy
        by_cases h : y ≤ 1
        · aesop
        field_simp
        simp only [mem_Ioc, h, and_false, ↓reduceIte, one_div, mul_zero]
        simp only [mem_Ioi] at hy
        apply div_nonneg
        · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
        · positivity
  have SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
      (ε_lt_one : ε < 1)
      (X : ℝ) (X_gt : 3 < X)
      {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
      (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
      (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
      (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
      (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
      (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
      (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
      SmoothedChebyshev SmoothingF ε X =
        I₁ SmoothingF ε X T -
        I₂ SmoothingF ε T X σ₁ +
        I₃₇ SmoothingF ε T X σ₁ +
        I₈ SmoothingF ε T X σ₁ +
        I₉ SmoothingF ε X T
        + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
    have Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
        (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
      unfold Smooth1 MellinConvolution DeltaSpike
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioi
      · intro y hy
        have ypos : 0 < y := mem_Ioi.mp hy
        have hν : 0 ≤ ν ((x / y) ^ (1 / ε)) :=
          νnonneg _ (rpow_pos_of_pos (div_pos xpos ypos) _)
        by_cases h : y ≤ 1
        · simpa [ypos, h] using (div_nonneg (div_nonneg hν εpos.le) ypos.le)
        · simp [ypos, h]
    have Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
        (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
        (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
        {s : ℂ} (hs : 0 < s.re) :
        DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
      apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
      · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
        apply continuousOn_of_forall_continuousAt
        exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
      · rw [Asymptotics.isBigO_iff]
        use 1
        obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
        filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
        rw [hc _ _ hε hx]
        simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
        bound
      · rw [Asymptotics.isBigO_iff]
        use 1
        filter_upwards [eventually_mem_nhdsWithin] with x hx
        simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
          mul_one]
        rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
        exact Smooth1LeOne Ψnonneg mass_one hε.1 hx
    have SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ}
        (ε_pos : 0 < ε) (ε_lt_one : ε < 1) {X : ℝ} (X_gt : 3 < X)
        {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
        (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
        (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
        (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
        (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
        Integrable (fun (t : ℝ) ↦
          SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
      have realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ)
          (hf : DifferentiableAt ℂ f s) :
          ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
        apply ContinuousAt.comp _ (by fun_prop)
        convert hf.continuousAt
        simp
      have MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
          (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
          ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
          (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
          ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
        obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
        refine ⟨C, Cpos, ?_⟩
        intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
        rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
        have hh1 : ε * σ₁ ≤ (ε * s).re := by
          simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
          nlinarith
        have hh2 : (ε * s).re ≤ 2 := by
          simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
          nlinarith
        calc
          ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
              ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
          _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
            gcongr
            convert! hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
            simp [abs_eq_self.mpr εpos.le]
          _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
            simp only [norm_inv, mul_inv_rev]
            ring
      have SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
          (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
          (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
          (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
          (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
          {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
          MeasureTheory.Integrable
            (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
        obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
        apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
        · apply Integrable.const_mul integrable_inv_one_add_sq
        · apply Continuous.aestronglyMeasurable
          apply continuous_iff_continuousAt.mpr
          intro x
          have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
            SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
              mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
          fun_prop
        · filter_upwards [] with t
          calc
            _≤ c / ε * 1 / (σ^2 + t^2) := by
              convert hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
                I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
                (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
                  sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
              simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
                mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
              ring_nf
            _ ≤ _ := by
              gcongr; nlinarith
      let C : ℝ := 1 + ‖ζ' σ₀ / ζ σ₀‖
      have hC (t : ℝ) : ‖ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ C := by
        have h := dlog_riemannZeta_bdd_on_vertical_lines_generalized
          σ₀ σ₀ t σ₀_gt (le_refl σ₀)
        rw [neg_div, norm_neg] at h
        exact le_trans h (lt_one_add _).le
      let c : ℝ := C * X ^ σ₀
      have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
        riemannZeta (σ₀ + (t : ℂ) * I) *
        (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
        intro t
        simp only [Complex.norm_mul, c]
        gcongr
        · convert! hC t using 1
          simp
        · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
          · simp
          · linarith
          · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
              mul_one, sub_self, add_zero, ne_eq]
            linarith
      convert (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
        suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul
          (c := c) ?_ (ae_of_all _ this) using 2
      · unfold SmoothedChebyshevIntegrand
        ring
      · apply Continuous.aestronglyMeasurable
        rw [← continuousOn_univ]
        intro t _
        let s := σ₀ + (t : ℂ) * I
        have s_ne_one : s ≠ 1 := by
          intro h
          have : σ₀ = 1 := by
            have := congr_arg Complex.re h
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
              mul_one, sub_self, add_zero, one_re, s] at this
            exact this
          linarith [σ₀_gt]
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.mul
        · have diffζ := differentiableAt_riemannZeta s_ne_one
          apply ContinuousAt.div
          · apply ContinuousAt.neg
            have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
              differentiableAt_deriv_riemannZeta s_ne_one
            convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) this <;> simp
          · convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
          · apply riemannZeta_ne_zero_of_one_lt_re
            simp [σ₀_gt]
        · apply ContinuousAt.comp _ (by fun_prop)
          apply continuousAt_const_cpow
          norm_cast
          linarith
    unfold SmoothedChebyshev
    unfold VerticalIntegral'
    have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
      nth_rewrite 1 [← add_zero 1]
      bound
    have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
      rw[← one_add_one_eq_two]
      gcongr
      exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
    have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
    rw [verticalIntegral_split_three (a := -T) (b := T)]
    swap
    · exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
        X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
    · have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
      unfold I₁
      simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc, add_left_cancel_iff]
      unfold I₉
      nth_rewrite 6 [add_comm]
      simp only [← add_assoc]
      rw [add_right_cancel_iff,
          ← add_right_inj (1 / (2 * ↑π * I) *
            -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
          ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
      unfold VIntegral I₂ I₃₇ I₈
      simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
      let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
        SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
      let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
      have : ∫ (y : ℝ) in -T..T,
          SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
          ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
          unfold fTempRR
          simp only [temp]
      rw[this]
      have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
          ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
          unfold fTempRR
          simp only [ofReal_neg, neg_mul, sub_eq_add_neg]
      rw[this]
      have : ∫ (t : ℝ) in -T..T,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
          ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := rfl
      rw[this]
      have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
          ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := rfl
      rw[this]
      have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
          -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
          I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
          ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
          -(2 * ↑π * I) * RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
          unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
          simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
            ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
            neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
            ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
            zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
          ring_nf
          simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
            mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
          ring_nf
      rw[this]
      field_simp
      rw[mul_comm, eq_comm, neg_add_eq_zero]

      have pInRectangleInterior :
          (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
        refine rectangle_mem_nhds_iff.mpr ?_
        refine mem_reProdIm.mpr ?_
        simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
          sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
        constructor
        · unfold uIoo
          rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          exact mem_Ioo.mpr ⟨σ₁_lt_one, (by linarith)⟩
        · unfold uIoo
          rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          exact mem_Ioo.mpr ⟨(by linarith), (by linarith)⟩

      apply ResidueTheoremOnRectangleWithSimplePole'
      · simp; linarith
      · simp; linarith
      · simp only [one_div]
        exact pInRectangleInterior
      · apply DifferentiableOn.mul
        · apply DifferentiableOn.mul
          · simp only [re_add_im]
            have : (fun z ↦ -ζ' z / ζ z) = -(ζ' / ζ) := by ext; simp; ring
            rw [this]
            apply DifferentiableOn.neg
            apply holoOn.mono
            apply Set.sdiff_subset_sdiff_left
            apply reProdIm_subset_iff'.mpr
            left
            simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
              div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
              neg_zero, zero_div, zero_add]
            constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
          · intro s hs
            apply DifferentiableAt.differentiableWithinAt
            simp only [re_add_im]
            apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
              SmoothingFnonneg mass_one
            have := mem_reProdIm.mp hs.1 |>.1
            simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
              div_self_mul_self', add_zero] at this
            rw [uIcc_of_le (by linarith)] at this
            linarith [this.1]
        · intro s hs
          apply DifferentiableAt.differentiableWithinAt
          simp only [re_add_im]
          apply DifferentiableAt.const_cpow (by fun_prop)
          left
          norm_cast
          linarith
      · let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
        let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
        let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
        unfold fTempC fTempRR SmoothedChebyshevIntegrand
        simp only [re_add_im]
        have g_holc : HolomorphicOn g U := by
          intro u uInU
          apply DifferentiableAt.differentiableWithinAt
          simp only [g]
          apply DifferentiableAt.mul
          · apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
              SmoothingFnonneg mass_one
            simp only [ofReal_inv, U] at uInU
            unfold Rectangle at uInU
            rw[Complex.mem_reProdIm] at uInU
            have := uInU.1
            simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
            rw [uIcc_of_le (by linarith)] at this
            linarith [this.1]
          · unfold HPow.hPow instHPow
            apply DifferentiableAt.const_cpow differentiableAt_fun_id
            left
            norm_cast
            linarith
        have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
          simp only [one_mul, f]
          exact riemannZetaLogDerivResidueBigO
        convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
        ext
        simp [f, g]
        ring
  have SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
      (X : ℝ) (_ : 3 < X)
      {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
      (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
      (σ₂_lt_σ₁ : σ₂ < σ₁)
      (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
      (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
        (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
      (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
      (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
      (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
      (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
      I₃₇ SmoothingF ε T X σ₁ =
        I₃ SmoothingF ε T X σ₁ -
        I₄ SmoothingF ε X σ₁ σ₂ +
        I₅ SmoothingF ε X σ₂ +
        I₆ SmoothingF ε X σ₁ σ₂ +
        I₇ SmoothingF ε T X σ₁ := by
    have Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
        (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
      unfold Smooth1 MellinConvolution DeltaSpike
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioi
      · intro y hy
        have ypos : 0 < y := mem_Ioi.mp hy
        have hν : 0 ≤ ν ((x / y) ^ (1 / ε)) :=
          νnonneg _ (rpow_pos_of_pos (div_pos xpos ypos) _)
        by_cases h : y ≤ 1
        · simpa [ypos, h] using (div_nonneg (div_nonneg hν εpos.le) ypos.le)
        · simp [ypos, h]
    have Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
        (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
        (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
        {s : ℂ} (hs : 0 < s.re) :
        DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
      apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
      · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
        apply continuousOn_of_forall_continuousAt
        exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
      · rw [Asymptotics.isBigO_iff]
        use 1
        obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
        filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
        rw [hc _ _ hε hx]
        simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
        bound
      · rw [Asymptotics.isBigO_iff]
        use 1
        filter_upwards [eventually_mem_nhdsWithin] with x hx
        simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
          mul_one]
        rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
        exact Smooth1LeOne Ψnonneg mass_one hε.1 hx
    have verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
        (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
        (hab : s < a ∧ a < b ∧ b < e) :
        VIntegral f σ s e = VIntegral f σ s a + VIntegral f σ a b +
          VIntegral f σ b e := by
      dsimp [VIntegral]
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := a),
        ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
      · ring
      all_goals
        apply IntervalIntegrable.mono_set hf
        apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith
    have SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
        (holoOn : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
        ContinuousOn (fun (t : ℝ) ↦ -ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))
          (Icc (-T) T) := by
      rw [show (fun (t : ℝ) ↦ -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) =
          -(ζ' / ζ) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
      apply ContinuousOn.neg
      apply holoOn.continuousOn.comp (by fun_prop)
      intro t ht
      simp only [Set.mem_sdiff, mem_singleton_iff]
      constructor
      · apply mem_reProdIm.mpr
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
        linarith
      · intro h
        replace h := congr_arg re h
        simp at h
        linarith
    have realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ)
        (hf : DifferentiableAt ℂ f s) :
        ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
      apply ContinuousAt.comp _ (by fun_prop)
      convert hf.continuousAt
      simp
    let z : ℂ := σ₂ - 3 * I
    let w : ℂ := σ₁ + 3 * I
    have σ₁_pos : 0 < σ₁ := by linarith
    -- Step (1)
    -- Show that the Rectangle is in a given subset of holomorphicity
    have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
      -- for every point x in the Rectangle
      intro x hx
      constructor
      · -- x is in the locus of holomorphicity
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx ⊢
        obtain ⟨hx_re, hx_im⟩ := hx
        -- the real part of x is in the correct interval
        have hzw_re : z.re < w.re := by
          simpa [z, w] using σ₂_lt_σ₁
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          simpa [min_eq_left hzw_re.le, max_eq_right hzw_re.le] using hx_re
        have x_re_in_Icc : x.re ∈ Icc σ₂ 2 := by
          have ⟨h_left, h_right⟩ := x_re_bounds
          have h_left' : σ₂ ≤ x.re := by
            simpa [z] using h_left
          have h_right' : x.re ≤ 2 := by
            apply le_trans h_right
            have : w.re ≤ 2 := by
              simp [w]
              linarith
            exact this
          exact ⟨h_left', h_right'⟩
        -- the imaginary part of x is in the correct interval
        have hzw_im : z.im < w.im := by
          norm_num [z, w]
        have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
          simpa [min_eq_left hzw_im.le, max_eq_right hzw_im.le] using hx_im
        have x_im_in_Icc : x.im ∈ Icc (-3) 3 := by
          have ⟨h_left, h_right⟩ := x_im_bounds
          have h_left' : -3 ≤ x.im := by
            simpa [z] using h_left
          have h_right' : x.im ≤ 3 := by
            simpa [w] using h_right
          exact ⟨h_left', h_right'⟩
        exact ⟨x_re_in_Icc, x_im_in_Icc⟩
      -- x is not in {1} by contradiction
      · simp only [mem_singleton_iff]
        -- x has real part less than 1
        have x_re_upper: x.re ≤ σ₁ := by
          simp only [Rectangle, uIcc] at hx
          rw [Complex.mem_reProdIm] at hx
          obtain ⟨hx_re, _⟩ := hx
          -- the real part of x is in the interval
          have hzw_re : z.re < w.re := by
            simpa [z, w] using σ₂_lt_σ₁
          have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
            simpa [min_eq_left hzw_re.le, max_eq_right hzw_re.le] using hx_re
          have x_re_upper' : x.re ≤ w.re := x_re_bounds.2
          have hw_re : w.re = σ₁ := by simp [w]
          linarith
        -- by contracdiction
        have h_x_ne_one : x ≠ 1 := by
          intro h_eq
          have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
          have h1 : 1 ≤ σ₁ := by
            rw [← h_re]
            exact x_re_upper
          linarith
        exact h_x_ne_one
    have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
    have splitting : I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
      unfold I₃₇ I₃ I₅ I₇
      have hsplit := verticalIntegral_split_three_finite
        (f := SmoothedChebyshevIntegrand SmoothingF ε X)
        (σ := σ₁) (s := -T) (a := -3) (b := 3) (e := T)
        (by
          apply ContinuousOn.integrableOn_Icc
          unfold SmoothedChebyshevIntegrand
          apply ContinuousOn.mul
          · apply ContinuousOn.mul
            · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
            · apply continuousOn_of_forall_continuousAt
              intro t t_mem
              have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
                SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
              simpa using realDiff_of_complexDiff _ this
          · apply continuousOn_of_forall_continuousAt
            intro t t_mem
            apply ContinuousAt.comp
            · refine continuousAt_const_cpow' ?_
              intro h
              have : σ₁ = 0 := by
                have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
                  rw [h]
                simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
                  sub_self, add_zero, zero_re] at h_real
                exact h_real
              linarith
            · -- continuity -- failed
              apply ContinuousAt.add
              · exact continuousAt_const
              · apply ContinuousAt.mul
                · apply continuous_ofReal.continuousAt
                · exact continuousAt_const)
        ⟨by linarith, by linarith, by linarith⟩
      dsimp only [VIntegral] at hsplit
      simp only [smul_eq_mul] at hsplit
      rw [hsplit]
      ring
    calc I₃₇ SmoothingF ε T X σ₁ =
          I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
      _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
          (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
      _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
          (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
          - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
          + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
          - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
        simp [RectangleIntegral]
      _ = I₃₇ SmoothingF ε T X σ₁ -
          ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
          - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
          + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
          - (1 / (2 * π * I)) *
              VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
      _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
      - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
      + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
      - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
        simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
          re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
          ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
          sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
          I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
        left
        rfl
      _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
      - I₆ SmoothingF ε X σ₁ σ₂
      + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
      - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
        simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
          re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
          ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
      _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
      - I₆ SmoothingF ε X σ₁ σ₂
      + I₅ SmoothingF ε X σ₁
      - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
        simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
          re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
          mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
          w, z]
      _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
      - I₆ SmoothingF ε X σ₁ σ₂
      + I₅ SmoothingF ε X σ₁
      - I₅ SmoothingF ε X σ₂) := by
        simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
          re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
          mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
      --- starting from now, we split the integral `I₃₇` into `I₃ σ₂ + I₅ σ₁ + I₇ σ₁` using `verticalIntegral_split_three_finite`
      _ = I₃ SmoothingF ε T X σ₁
      + I₅ SmoothingF ε X σ₁
      + I₇ SmoothingF ε T X σ₁
      - (I₄ SmoothingF ε X σ₁ σ₂
      - I₆ SmoothingF ε X σ₁ σ₂
      + I₅ SmoothingF ε X σ₁
      - I₅ SmoothingF ε X σ₂) := by
        rw [splitting]
      _ = I₃ SmoothingF ε T X σ₁
      - I₄ SmoothingF ε X σ₁ σ₂
      + I₅ SmoothingF ε X σ₂
      + I₆ SmoothingF ε X σ₁ σ₂
      + I₇ SmoothingF ε T X σ₁ := by
        ring
  have I5Bound {SmoothingF : ℝ → ℝ}
      (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
      (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
      {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
      : ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
      (_ : ε < 1),
      ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by
    have MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
        (suppν : ν.support ⊆ Icc (1 / 2) 2) :
        ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
          (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
          ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
      obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
      refine ⟨C, Cpos, ?_⟩
      intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
      rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
      have hh1 : ε * σ₁ ≤ (ε * s).re := by
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
        nlinarith
      have hh2 : (ε * s).re ≤ 2 := by
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
        nlinarith
      calc
        ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
            ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
        _ ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
          gcongr
          convert! hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
          simp [abs_eq_self.mpr εpos.le]
        _ = C * (ε * ‖s‖ ^ 2)⁻¹ := by
          simp only [norm_inv, mul_inv_rev]
          ring
    unfold LogDerivZetaIsHoloSmall HolomorphicOn at h_logDeriv_holo
    let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)

    have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
      simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
        Nat.ofNat_nonneg, uIcc_of_le]
      intro z hyp_z
      simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
      simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff]
      constructor
      · constructor
        · rw [hyp_z.1]
          apply left_mem_uIcc
        · exact hyp_z.2
      · push Not
        by_contra h
        rw [h] at hyp_z
        simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
        linarith [hσ₂.2]

    have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

    have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
      refine IsCompact.reProdIm ?_ ?_
      · exact isCompact_singleton
      · exact isCompact_uIcc

    let ⟨zeta_bound, zeta_prop⟩ :=
      IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

    let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
      MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

    clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

    unfold I₅
    unfold SmoothedChebyshevIntegrand

    let mellin_prop : ∀ (t ε : ℝ),
    0 < ε → ε < 1 → ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
      fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
        ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

    simp only [mul_inv_rev] at mellin_prop

    let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

    let C := |π|⁻¹ * 2⁻¹ * 6 * Const
    use C
    have C_pos : 0 < C := by positivity
    use C_pos

    clear C_pos

    intros X X_gt ε ε_pos ε_lt_one

    have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

    have U: 0 < σ₂^2 := by
      exact sq_pos_of_pos (by linarith[hσ₂.1])

    have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
      by
        intro t
        rw [inv_le_inv₀]
        · rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero, add_im, mul_im, zero_add]
          ring_nf
          simp only [le_add_iff_nonneg_right]
          exact zpow_two_nonneg t
        · rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero, add_im, mul_im, zero_add]
          ring_nf
          positivity
        positivity

    have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
            (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
      intro t hyp_t
      have Z := by
        calc
          ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
            Complex.norm_div, norm_neg]
          _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
            norm_neg, le_refl]
          _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
            by
              have U := zeta_prop (↑σ₂ + t * I) (by
                  simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                  simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                    mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                  constructor
                  · trivial
                  · refine mem_Icc.mp ?_
                    · refine mem_Icc_of_Ioc ?_
                      · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                        rw [←Set.uIoc_of_le T]
                        exact hyp_t)
              simp only [Complex.norm_div] at U
              simp only [Complex.norm_div, ge_iff_le]
              linear_combination U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
          _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
            have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
            linear_combination (U * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
          _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
            have U := mellin_bound t
            linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
          _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
            linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
          _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos]
            · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
                sub_self, add_zero]
            positivity
          _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
            unfold Const
            ring_nf
            simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
            positivity

      exact Z

    -- Now want to apply the triangle inequality
    -- and bound everything trivially
    simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
      norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
    have Z :=
      intervalIntegral.norm_integral_le_of_norm_le_const T1
    simp only [ge_iff_le]

    have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε := by
      unfold C
      ring_nf

    simp only [sub_neg_eq_add] at Z
    simp only [← S, ge_iff_le]
    linear_combination (|π|⁻¹ * 2⁻¹ * Z)
  obtain ⟨C₅, C₅pos, hI5⟩ :=
    I5Bound suppSmoothingF ContDiffSmoothingF holoSmall hσ₂
  refine ⟨C₅, C₅pos, ?_⟩
  intro X ε T σ₁ X_gt ε_pos ε_lt_one T_pos σ₁_pos σ₁_lt_one σ₂_lt_σ₁ holoOn holoOn2
  have hContour :
      ‖SmoothedChebyshev SmoothingF ε X -
          𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X‖ ≤
        ‖I₁ SmoothingF ε X T‖ + ‖I₂ SmoothingF ε T X σ₁‖ +
        ‖I₃ SmoothingF ε T X σ₁‖ + ‖I₄ SmoothingF ε X σ₁ σ₂‖ +
        ‖I₅ SmoothingF ε X σ₂‖ + ‖I₆ SmoothingF ε X σ₁ σ₂‖ +
        ‖I₇ SmoothingF ε T X σ₁‖ + ‖I₈ SmoothingF ε T X σ₁‖ +
        ‖I₉ SmoothingF ε X T‖ := by
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt (T := T) (by linarith : 0 < T)
      σ₁_pos σ₁_lt_one holoOn suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt (T := T) T_pos
      hσ₂.1 σ₁_lt_one σ₂_lt_σ₁ holoOn holoOn2 suppSmoothingF SmoothingFnonneg mass_one
      ContDiffSmoothingF]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    rw [(by ring : I₁ SmoothingF ε X T - I₂ SmoothingF ε T X σ₁ +
      I₃ SmoothingF ε T X σ₁ - I₄ SmoothingF ε X σ₁ σ₂ =
      (I₁ SmoothingF ε X T - I₂ SmoothingF ε T X σ₁) +
      (I₃ SmoothingF ε T X σ₁ - I₄ SmoothingF ε X σ₁ σ₂))]
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ SmoothingF ε X T‖ + ‖I₂ SmoothingF ε T X σ₁‖ +
      ‖I₃ SmoothingF ε T X σ₁‖ + ‖I₄ SmoothingF ε X σ₁ σ₂‖ =
      (‖I₁ SmoothingF ε X T‖ + ‖I₂ SmoothingF ε T X σ₁‖) +
      (‖I₃ SmoothingF ε T X σ₁‖ + ‖I₄ SmoothingF ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
  have hI5point := hI5 X X_gt ε_pos ε_lt_one
  apply le_trans hContour
  gcongr <;> exact hI5point
