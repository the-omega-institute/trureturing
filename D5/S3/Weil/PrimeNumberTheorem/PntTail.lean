/- GID: D5/S3/Weil/PrimeNumberTheorem/PntTail
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeNumberTheorem/PntTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The smoothed Chebyshev contour has controlled vertical and horizontal tails. -/

/-
Source: AlexKontorovich/PrimeNumberTheoremAnd, revision 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.
Original file: PrimeNumberTheoremAnd/MediumPNT.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Full license and upstream attribution: Library/Weil/primenumbertheoremand2026medium.md.
This file is modified from the cited source.
Retirement: replace this consumed closure with direct references when this
repository's adopted Mathlib revision contains equivalent quantified contracts.
-/

import D5.S3.Weil.PrimeNumberTheorem.PntSmoothing

set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory ComplexConjugate
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin
local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))

def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})

set_option maxHeartbeats 800000 in
theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
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
  have integral_evaluation (x : ℝ) (T : ℝ) (T_large : 3 < T) :
      ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
    have ae_volume_of_contains_compl_singleton_zero
        (s : Set ℝ) (h : (univ : Set ℝ) \ {0} ⊆ s) : s ∈ ae volume := by
      have h_zero_null : volume ({0} : Set ℝ) = 0 := volume_singleton
      have h_compl_subset : sᶜ ⊆ {0} := by
        intro y hy
        by_contra h_not_zero
        exact hy (h ⟨trivial, h_not_zero⟩)
      have h_compl_measure : volume sᶜ ≤ volume ({0} : Set ℝ) :=
        measure_mono h_compl_subset
      have h_compl_zero : volume sᶜ = 0 := by
        rw [h_zero_null] at h_compl_measure
        exact le_antisymm h_compl_measure (by positivity)
      rwa [mem_ae_iff]
    have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
      intro x t
      rw [Complex.norm_add_mul_I x t]
      ring_nf
      rw [Real.sq_sqrt _]
      · simp only [le_add_iff_nonneg_right]; positivity
      · positivity

    have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
      intro x t hyp
      have U0 : 0 < t^2 := by positivity
      have U1 : 0 < ‖x + t * I‖^2 := by
        rw [Complex.norm_add_mul_I x t,
          Real.sq_sqrt _]

        · positivity
        · positivity
      rw [inv_le_inv₀ U1 U0]
      exact (T00 x t)

    have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
      unfold Filter.EventuallyLE
      unfold Filter.Eventually
      simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
      refine mem_inf_of_left ?_
      · refine Filter.mem_sets.mp ?_
        · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
            rw [Set.setOf_subset_setOf]
            intro t hyp_t
            exact T0 x t hyp_t
          have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
            apply Set.ext
            intro x
            simp_all only [ne_eq, setOf_subset_setOf, not_false_eq_true, implies_true,
              mem_setOf_eq, Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and]

          rw [U1] at U
          exact ae_volume_of_contains_compl_singleton_zero _ U

    have T3 : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
      have D3 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by linarith : 0 < T) |>.comp_neg
      simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
      have D4 :=
        (integrableOn_Iic_iff_integrableOn_Iio'
          (by
            refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
            simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, measure_singleton,
              EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
      simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
      unfold IntegrableOn at D4
      have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
        funext x
        simp_all only [even_two, Even.neg_pow]
      simp_all only [even_two, Even.neg_pow]
      norm_cast at D4
      simp_all only [even_two, Even.neg_pow]

    calc
      _ ≤ ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹  := by
        apply MeasureTheory.integral_mono_of_nonneg _ T3 T1
        filter_upwards [] with x
        simp
      _ = _ := by
        rw [← integral_comp_neg_Ioi]
        conv => lhs; arg 2; ext x; rw [show ((-x) ^ 2)⁻¹ = x ^ (-2 : ℝ) by simp [zpow_ofNat]]
        rw[integral_Ioi_rpow_of_lt (by norm_num) (by linarith)]
        ring_nf
        rw [rpow_neg_one]
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
  obtain ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  have G0 : ∃K > 0, ∀(t σ : ℝ), 1 < σ → σ < 2 → ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    let ⟨K', ⟨K'_pos, K'_bounds_zeta⟩⟩ := triv_bound_zeta
    use (2 * (K' + 1))
    use (by positivity)
    intro t σ cond cond2

    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, ge_iff_le, Complex.norm_div,
        norm_neg, tsub_le_iff_right, inv_one]

    have T : (K' + 1) * 1 ≤ (K' + 1) * (σ - 1)⁻¹ :=
      by
        exact (mul_le_mul_iff_right₀ T0).mpr T1
    have U := calc
      ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ = ‖-ζ' (σ + t * I) / ζ (σ + t * I)‖ := by
        rw [← norm_neg _, mul_comm, neg_div' _ _]
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds_zeta σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by aesop
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by linarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by
        ring_nf

    exact U

  obtain ⟨K, ⟨K_is_pos, K_bounds_zeta_at_any_t'⟩⟩ := G0

  have C_final_pos : |π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M) > 0 := by
    positivity

  use (|π|⁻¹ * 2⁻¹ * (Real.exp 1 * K * M))
  use C_final_pos

  intro eps eps_pos eps_less_one X X_large T T_large

  let pts_re := 1 + (Real.log X)⁻¹
  let pts := fun (t : ℝ) ↦ (pts_re + t * I)

  have pts_re_triv : ∀(t : ℝ), (pts t).re = pts_re := by
    intro t
    unfold pts
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]

  have pts_re_ge_one : 1 < pts_re := by
    unfold pts_re
    simp only [lt_add_iff_pos_right, inv_pos]
    have U : 1 < X := by linarith
    exact Real.log_pos U

  have pts_re_le_one : pts_re < 2 := by
    unfold pts_re
    have Z : Real.log 3 < Real.log X :=
      by
        refine log_lt_log ?_ X_large
        simp only [Nat.ofNat_pos]

    have Z01 : 1 < Real.log 3 := logt_gt_one le_rfl
    have Zpos0 : 0 < Real.log 3 := by positivity
    have Zpos1 : 0 < Real.log X := by calc
      0 < Real.log 3 := Zpos0
      _ < Real.log X := Z

    have Z1 : (Real.log X)⁻¹ < (Real.log 3)⁻¹ := (inv_lt_inv₀ Zpos1 Zpos0).mpr Z

    have Z02 : (Real.log 3)⁻¹ < 1 := by
      have T01 := (inv_lt_inv₀ ?_ ?_).mpr Z01
      · simp only [inv_one] at T01
        exact T01
      · exact Zpos0
      simp only [zero_lt_one]

    have Z2 : 1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := by
      exact (add_lt_add_iff_left 1).mpr Z1

    have Z3 : 1 + (Real.log 3)⁻¹ < 2 := by
      calc
        1 + (Real.log 3)⁻¹ < 1 + 1 := by linarith
        _ = 2 := by ring_nf

    calc
      1 + (Real.log X)⁻¹ < 1 + (Real.log 3)⁻¹ := Z2
      _ < 2 := Z3

  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    unfold pts_re
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, add_sub_cancel_left, inv_inv]

  have K_bounds_zeta_at_any_t :
      ∀(t : ℝ), ‖ζ' (pts t) / ζ (pts t)‖ ≤ K * Real.log X := by
    intro t
    rw [←inve]
    exact K_bounds_zeta_at_any_t' t pts_re pts_re_ge_one pts_re_le_one

  have pts_re_pos : pts_re > 0 := by
    unfold pts_re
    positivity

  have triv_pts_lo_bound : ∀(t : ℝ), pts_re ≤ (pts t).re := by
    intro t
    unfold pts_re
    exact Eq.ge (pts_re_triv t)

  have triv_pts_up_bound : ∀(t : ℝ), (pts t).re ≤ 2 := by
    intro t
    unfold pts
    refine EReal.coe_le_coe_iff.mp ?_
    · simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
      Complex.norm_div, le_refl, implies_true, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero, EReal.coe_le_coe_iff]
      exact le_of_lt pts_re_le_one

  have pts_re_ge_1 : pts_re > 1 := by
    unfold pts_re
    exact pts_re_ge_one

  have X_pos_triv : 0 < X := by positivity

  let f := fun (t : ℝ) ↦ SmoothedChebyshevIntegrand SmoothingF eps X (pts t)

  /- Main pointwise bound -/

  have G : ∀(t : ℝ), ‖f t‖ ≤ (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by

    intro t

    let M_bounds_mellin_easy := fun (t : ℝ) ↦
      M_bounds_mellin_hard pts_re pts_re_pos (pts t) (triv_pts_lo_bound t) (triv_pts_up_bound t)
        eps eps_pos eps_less_one

    let zeta_part := (fun (t : ℝ) ↦ -ζ' (pts t) / ζ (pts t))
    let mellin_part := (fun (t : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF eps x : ℂ)) (pts t))
    let X_part := (fun (t : ℝ) ↦ (↑X : ℂ) ^ (pts t))

    let g := fun (t : ℝ) ↦ (zeta_part t) * (mellin_part t) * (X_part t)

    have X_part_eq : ∀(t : ℝ), ‖X_part t‖ = X^pts_re := by
      intro t
      have U := Complex.norm_cpow_eq_rpow_re_of_pos (X_pos_triv) (pts t)
      rw [pts_re_triv t] at U
      exact U

    have X_part_bound : ∀(t : ℝ), ‖X_part t‖ ≤ X^pts_re := by
      intro t
      rw [←X_part_eq]

    have mellin_bound : ∀(t : ℝ), ‖mellin_part t‖ ≤ M * (eps * ‖pts t‖ ^ 2)⁻¹ := by
      intro t
      exact M_bounds_mellin_easy t

    have X_part_and_mellin_bound :
        ∀(t : ℝ), ‖mellin_part t * X_part t‖ ≤ M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by
      intro t
      exact norm_mul_le_of_le (mellin_bound t) (X_part_bound t)

    have T2 : ∀(t : ℝ), ‖zeta_part t‖ = ‖ζ' (pts t) / ζ (pts t)‖ := by
      intro t
      unfold zeta_part
      simp only [Complex.norm_div, norm_neg]

    have zeta_bound : ∀(t : ℝ), ‖zeta_part t‖ ≤ K * Real.log X := by
      intro t
      unfold zeta_part
      rw [T2]
      exact K_bounds_zeta_at_any_t t

    have g_bound : ∀(t : ℝ), ‖zeta_part t * (mellin_part t * X_part t)‖ ≤
        (K * Real.log X) * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      intro t
      exact norm_mul_le_of_le (zeta_bound t) (X_part_and_mellin_bound t)

    have T1 : f = g := rfl

    have final_bound_pointwise :
        ‖f t‖ ≤ K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) := by
      rw [T1]
      unfold g
      rw [mul_assoc]
      exact g_bound t

    have trivialize :
        K * Real.log X * (M * (eps * ‖pts t‖^2)⁻¹ * X^pts_re) =
          (K * M) * Real.log X * (eps * ‖pts t‖^2)⁻¹ * X^pts_re := by ring_nf

    rw [trivialize] at final_bound_pointwise
    exact final_bound_pointwise

  have σ₀_gt : 1 < pts_re := pts_re_ge_1
  have σ₀_le_2 : pts_re ≤ 2 := by
    unfold pts_re
    -- LOL!
    exact
      Preorder.le_trans (1 + (Real.log X)⁻¹) (pts (SmoothingF (SmoothingF M))).re 2
        (triv_pts_lo_bound (SmoothingF (SmoothingF M)))
        (triv_pts_up_bound (SmoothingF (SmoothingF M)))

  have f_integrable := SmoothedChebyshevPull1_aux_integrable eps_pos eps_less_one X_large σ₀_gt
    σ₀_le_2 suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF

  have S : X^pts_re = rexp 1 * X := by
    unfold pts_re

    calc
      X ^ (1 + (Real.log X)⁻¹) = X * X ^ ((Real.log X)⁻¹) := by
        refine rpow_one_add' ?_ ?_
        · positivity
        · exact Ne.symm (ne_of_lt pts_re_pos)
      _ = X * rexp 1 := by
        refine (mul_right_inj' ?_).mpr ?_
        · exact Ne.symm (ne_of_lt X_pos_triv)
        · refine rpow_inv_log X_pos_triv ?_
          · by_contra h
            simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
              Complex.norm_div, Nat.not_ofNat_lt_one]
      _ = rexp 1 * X := by ring_nf

  have pts_re_neq_zero : pts_re ≠ 0 := by
    by_contra h
    rw [h] at pts_re_ge_1
    simp only [gt_iff_lt] at pts_re_ge_1
    norm_cast at pts_re_ge_1

  have Z :=
    by
      calc
        ‖∫ (t : ℝ) in Iic (-T), f t‖ ≤ ∫ (t : ℝ) in Iic (-T), ‖f t‖ := MeasureTheory.norm_integral_le_integral_norm f
        _ ≤ ∫ (t : ℝ) in Iic (-T), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re := by
            refine integral_mono ?_ ?_ (fun t ↦ G t)
            · refine Integrable.norm ?_
              · unfold f
                exact MeasureTheory.Integrable.restrict f_integrable
            · have equ : ∀(t : ℝ), (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re = (K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹ := by
                   intro t; ring_nf
              have fun_equ : (fun (t : ℝ) ↦ ((K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re)) = (fun (t : ℝ) ↦ ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re * (‖pts t‖^2)⁻¹)) := by
                   funext t
                   exact equ t

              rw [fun_equ]
              have simple_int : MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
                := by
                   unfold pts
                   have h1 : ∀ t : ℝ, ‖pts_re + t * I‖^2 = pts_re^2 + t^2 := by
                     intro t
                     rw [← normSq_eq_norm_sq, normSq_add_mul_I]
                   simp_rw [h1]
                   apply integrable_comp_mul_left_iff _ pts_re_neq_zero |>.mp
                   have : (fun t ↦ (pts_re ^ 2 + (pts_re * t) ^ 2)⁻¹) =
                       (fun t ↦ (1 / pts_re ^ 2) * (1 + t ^ 2)⁻¹) := by
                     ext
                     field_simp
                   rw [this]
                   exact integrable_inv_one_add_sq.const_mul (1 / pts_re ^ 2)

              have U := MeasureTheory.Integrable.const_mul simple_int
                ((K * M) * Real.log X * eps⁻¹ * X ^ pts_re)
              refine MeasureTheory.Integrable.restrict ?_
              exact U
        _ = (K * M) * Real.log X * X ^ pts_re * eps⁻¹ *
              ∫ (t : ℝ) in Iic (-T), (‖pts t‖ ^ 2)⁻¹ := by
              have simpli_fun :
                  (fun (t : ℝ) ↦ (K * M) * Real.log X * (eps * ‖pts t‖ ^ 2)⁻¹ * X ^ pts_re) =
                    (fun (t : ℝ) ↦ ((K * M) * Real.log X * X ^ pts_re * eps⁻¹ * (‖pts t‖^2)⁻¹)) :=
                by funext t; ring_nf
              rw [simpli_fun]
              exact MeasureTheory.integral_const_mul ((K * M) * Real.log X * X ^ pts_re * eps⁻¹)
                (fun (t : ℝ) ↦ (‖pts t‖^2)⁻¹)
        _ ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ * T⁻¹ := by
              have U := integral_evaluation (pts_re) T (T_large)
              unfold pts
              simp only [ge_iff_le]
              have U2 : 0 ≤ (K * M) * Real.log X * X ^ pts_re * eps⁻¹ := by
                simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, mul_inv_rev, gt_iff_lt,
                  Complex.norm_div, le_refl, implies_true, inv_pos, mul_nonneg_iff_of_pos_right]
                refine Left.mul_nonneg ?_ ?_
                · refine Left.mul_nonneg ?_ ?_
                  · exact Left.mul_nonneg (by positivity) (by positivity)
                  · refine log_nonneg ?_
                    · linarith
                · refine Left.mul_nonneg ?_ ?_
                  · exact exp_nonneg 1
                  · exact le_of_lt X_pos_triv
              exact mul_le_mul_of_nonneg_left U U2
        _ = (Real.exp 1 * K * M) * Real.log X * X * eps⁻¹ * T⁻¹ := by
          rw [S]
          ring_nf
        _ = (Real.exp 1 * K * M) * X * Real.log X / (eps * T) := by ring_nf

  unfold I₁
  unfold f at Z
  unfold pts at Z
  have Z3 : (↑pts_re : ℂ) = 1 + (Real.log X)⁻¹ := by unfold pts_re; norm_cast
  rw [Z3] at Z
  rw [Complex.norm_mul (1 / (2 * ↑π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  simp only [ofReal_inv] at Z
  simp only [ge_iff_le]
  have Z4 := mul_le_mul_of_nonneg_left Z Z2
  ring_nf
  ring_nf at Z4
  exact Z4

lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  have IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) (k : ℕ) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
    -- When X is large, the ratio goes to 0.
    have ⟨M, hM⟩ := Filter.eventually_atTop.mp (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
    -- When X is small, use the extreme value theorem.
    let f := fun X ↦ Real.log X ^ k / X
    let I := Icc X₀ M
    have : 0 ∉ I := notMem_Icc_of_lt X₀pos
    have f_cont : ContinuousOn f (Icc X₀ M) :=
      ((continuousOn_log.pow k).mono (subset_compl_singleton_iff.mpr this)).div
      continuous_id.continuousOn (fun x hx ↦ ne_of_mem_of_not_mem hx this)
    have ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn f_cont
    use max C₁ 1, le_max_right C₁ 1
    intro X hX
    have Xpos : X > 0 := lt_of_lt_of_le X₀pos hX
    by_cases hXM : X ≤ M
    · rw[← div_le_iff₀ Xpos]
      calc
        f X ≤ ‖f X‖ := le_norm_self _
        _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
        _ ≤ max C₁ 1 := le_max_left C₁ 1
    · calc
        Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_norm_self _
        _ ≤ ‖X ^ 1‖ := by exact_mod_cast hM X (by linarith[hXM])
        _ = 1 * X := by
          rw[pow_one, one_mul]
          apply norm_of_nonneg
          exact Xpos.le
        _ ≤ max C₁ 1 * X := by
          rw[mul_le_mul_iff_left₀ Xpos]
          exact le_max_right C₁ 1
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
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) 9)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
  have one_add_inv_log : 1 + (Real.log X)⁻¹ < 2 := by
    rw [← one_add_one_eq_two]
    exact (add_lt_add_iff_left 1).mpr (inv_lt_one_of_one_lt₀ (logt_gt_one X_gt.le))
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    dsimp[σ₁]
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_right
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      · exact A_in.1.le
      apply pow_nonneg
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have σ₁pos : 0 < σ₁ := by
    rw[sub_pos]
    calc
      A / Real.log T ^ 9 ≤ 1 / 2 / Real.log T ^ 9 := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply pow_nonneg
        rw[log_nonneg_iff Tpos]
        exact le_trans (by norm_num) (le_of_lt T_gt)
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        exact one_le_pow₀ (logt_gt_one T_gt.le).le
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert this using 3
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        · rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
          calc
            1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
            _ ≤ 2 := one_add_inv_log.le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
  -- Now bound the integrand
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ 9 := has_bound σ (-T)
          (by simp only [abs_neg]; rw [abs_of_pos Tpos]; exact T_gt)
          (by unfold σ₁ at hσ; simp only [mem_Ioc, abs_neg, log_abs, mem_Ici,
            tsub_le_iff_right] at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ 9 := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  -- Then estimate the remaining factors.
  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero, σ₁] at hσ ⊢
          linarith[one_add_inv_log.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          · simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
              sub_zero]
            rw [← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
            · exact hσ.2
            · refine (Real.log_pos ?_).ne.symm
              linarith
            · apply Real.log_pos
              linarith
            · linarith
            · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          · exact this
          · exact ε_pos
          · positivity
          · apply mul_pos ε_pos
            exact lt_of_lt_of_le (pow_pos Tpos 2) this
          · positivity
        _ = C' * X / (ε * T) := by
          field_simp
