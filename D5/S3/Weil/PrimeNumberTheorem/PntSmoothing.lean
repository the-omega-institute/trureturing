/- GID: D5/S3/Weil/PrimeNumberTheorem/PntSmoothing
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeNumberTheorem/PntSmoothing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The smoothed Chebyshev integral has a quantified smoothing error. -/

/-
Source: AlexKontorovich/PrimeNumberTheoremAnd, revision 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.
Original file: PrimeNumberTheoremAnd/MediumPNT.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Full license and upstream attribution: Library/Weil/primenumbertheoremand2026medium.md.
This file is modified from the cited source.
Retirement: replace this consumed closure with direct references when this
repository's adopted Mathlib revision contains equivalent quantified contracts.
-/

import D5.S3.Weil.PrimeNumberTheorem.Smooth1
import D5.S3.Weil.ZetaPntBounds.ZetaBoundsLogDerivative
import D5.S3.Weil.ZetaPntBase.ZetaConj
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev


local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open MeasureTheory

attribute [fun_prop] Continuous.const_cpow

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X := by
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
  have SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
      (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
      (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
      (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
      (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
      {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
      SmoothedChebyshev SmoothingF ε X =
        ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
    have SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
        (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
        (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
        (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
        (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
        (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
        (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
        ∫ (t : ℝ),
          ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
        ∑' (n : ℕ),
          ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
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

      have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
          𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
        rw [← continuousOn_univ]
        refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
        · refine continuousOn_of_forall_continuousAt ?_
          intro z hz
          exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
            SmoothingFpos mass_one hz).continuousAt
        · fun_prop
        · simp only [mapsTo_univ_iff, mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
            ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

      have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
        intro a i
        simp_rw [← norm_toNNReal]
        rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
          ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
        norm_cast

      rw [MeasureTheory.integral_tsum]
      · have x_neq_zero : X ≠ 0 := by linarith
        intro i
        by_cases i_eq_zero : i = 0
        · simpa [i_eq_zero] using aestronglyMeasurable_const
        · apply Continuous.aestronglyMeasurable
          fun_prop (disch := simp[i_eq_zero, x_neq_zero])
      · rw [← lt_top_iff_ne_top]
        simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
          Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
        simp only [nnnorm_real, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero]
        simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
          ENNReal.tsum_mul_right]
        apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top

        conv =>
          arg 1
          arg 1
          intro i
          rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

        rw [ENNReal.tsum_mul_right]
        apply WithTop.mul_lt_top
        · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
          push_cast
          convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
            (by simp only [ofReal_re]; linarith)).norm
          rw [LSeries.term_def]
          split_ifs with h <;> simp[h]
        · simp_rw [← enorm_eq_nnnorm]
          rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
          exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
                mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral
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
    dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
    set σ : ℝ := 1 + (Real.log X)⁻¹
    have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
    have σ_gt : 1 < σ := by
      simp only [σ]
      have : 0 < (Real.log X)⁻¹ := by
        simp only [inv_pos]
        linarith
      linarith
    have σ_le : σ ≤ 2 := by
      simp only [σ]
      have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
      linarith
    calc
      _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, Λ n / (n : ℂ) ^ (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
      _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), Λ n / (n : ℂ) ^ (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
      _ = 1 / (2 * π * I) * (I * ∑' n, Λ n * ∫ (t : ℝ),
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
          (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
      _ = 1 / (2 * π) * (∑' n, Λ n * ∫ (t : ℝ),
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
          (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
      _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
          (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
      _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
          ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
      _ = _ := ?_
    · congr; ext t
      have hLogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
          - deriv riemannZeta s / riemannZeta s =
            ∑' n, Λ n / (n : ℂ) ^ s := by
        rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
        dsimp [LSeries, LSeries.term]
        nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
        · simp
        · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
          dsimp [LSeriesSummable] at this
          convert! this; rename ℕ => n
          by_cases h : n = 0 <;> simp [LSeries.term, h]
      rw [hLogDerivativeDirichlet]
      · rw [← tsum_mul_right, ← tsum_mul_right]
      · simp [σ_gt]
    · congr
      exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
    · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
      by_cases n_ne_zero : n = 0
      · simp [n_ne_zero]
      rw [mul_div_assoc, mul_assoc]
      congr
      rw [(div_eq_iff ?_).mpr]
      · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
        · push_cast at this ⊢
          rw [← this, div_mul_cancel₀]
          · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
        · apply div_nonneg (by linarith : 0 ≤ X); simp
        · simp
      · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
          not_false_eq_true]
    · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
    · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
    · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
      have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
      have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
        simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
      have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
          ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
        rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
      conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
    · push_cast
      congr
      ext n
      by_cases n_zero : n = 0
      · simp [n_zero]
      have n_pos : 0 < n := by
        simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
      congr
      have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
        ?_ ?_ ?_ ?_
      · beta_reduce at this
        dsimp [mellinInv, VerticalIntegral] at this
        convert! this using 4
        · norm_cast
        · rw [mul_comm]
          norm_cast
      · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
      · apply mellinConvergent_of_isBigO_rpow_exp (b := 0) zero_lt_one _ _ _
          (by simp only [ofReal_re]; linarith)
        · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
          apply continuousOn_of_forall_continuousAt
          exact fun x hx ↦
            (Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF εpos hx).ofReal
        · rw [Asymptotics.isBigO_iff]
          use 1
          obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppSmoothingF
          filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
          rw [hc _ _ ⟨εpos, ε_lt_one⟩ hx]
          simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
          bound
        · rw [Asymptotics.isBigO_iff]
          use 1
          filter_upwards [eventually_mem_nhdsWithin] with x hx
          simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem,
            CStarRing.norm_of_mem_unitary, mul_one]
          rw [_root_.abs_of_nonneg <| Smooth1Nonneg SmoothingFpos hx εpos]
          exact Smooth1LeOne SmoothingFpos mass_one εpos hx
      · dsimp [VerticalIntegrable]
        apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
          suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
      · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
        exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
          εpos (by positivity)
  have SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
      (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
      (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
      (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
      (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
      (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
      (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
      (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
      (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
      (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
      (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) →
        Smooth1 SmoothingF ε (↑n / X) = 1)
      (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
    ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
        ψ X‖ ≤
      C * ε * X * Real.log X := by
    norm_cast

    let F := Smooth1 SmoothingF ε

    let n₀ := ⌈X * (1 - c₁ * ε)⌉₊

    have n₀_pos : 0 < n₀ := by
      simp only [Nat.ceil_pos, n₀]
      subst C_eq
      simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos]
      exact mul_lt_one_of_nonneg_of_lt_one_left c₁_pos.le c₁_lt ε_lt_one.le

    have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
      nth_rewrite 2 [← mul_one X]
      apply mul_le_mul_of_nonneg_left _ X_pos.le
      apply sub_le_self
      positivity

    have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
      simp only [n₀]
      exact le_of_lt (Nat.ceil_lt_add_one (by bound))

    have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
      simp only [n₀]
      exact Nat.le_ceil (X * (1 - c₁ * ε))

    have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by
      exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
      (hc₂ _ _ (⟨ε_pos, ε_lt_one⟩) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
      (s ∘ Finset.mem_range.2))))))

    have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by
      exact_mod_cast sumΛ.comp_injective fun Q => by omega

    rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumΛn₀ n₀)]

    let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

    have n₁_pos : 0 < n₁ := by
      dsimp only [n₁]
      apply Nat.le_floor
      rw[Nat.succ_eq_add_one, zero_add]
      norm_cast
      apply one_le_mul_of_one_le_of_one_le (by linarith)
      apply le_add_of_nonneg_right
      positivity

    have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
      simp only [tsub_le_iff_right, n₁]
      exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

    have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
      simp only [n₁]
      exact Nat.floor_le (by bound)

    have n₁_ge_n₀ : n₀ ≤ n₁ := by
      exact_mod_cast le_imp_le_of_le_of_le n₀_le n₁_ge (by linarith)

    have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
      calc
        (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                          exact sub_le_sub_right n₁_le ↑n₀
         _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
            exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
         _            = X * ε * (c₂ + c₁) := by ring

    rw[show (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) =
        (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((n + n₀) / X)) +
        (∑' (n : ℕ), Λ (n + n₁ : ) * F ((n + n₁ : ) / X)) by
      rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
      · congr! 5
        · simp only [Nat.cast_add]
        · omega
        · congr! 1
          norm_cast
          omega
      · convert sumΛn₀ ((n₁ - n₀) + n₀) using 4
        · omega
        · congr! 1
          norm_cast
          omega]

    rw [show(∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) by
      have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) =
          Λ (n₁) * F (↑n₁ / X) + (∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) := by
        let fTemp := fun n ↦ Λ (n + n₁) * F ((↑n + ↑n₁) / X)
        have hTemp (n : ℕ): fTemp n = Λ (n + n₁) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
        rw[← tsum_congr hTemp, ← tsum_congr fun n ↦ (hTemp (n + 1))]
        have : Λ n₁ * F (↑n₁ / X) = fTemp 0 := by
          dsimp only [fTemp]
          rw[← Nat.cast_add, zero_add]
        rw[this]
        exact Summable.tsum_eq_zero_add (sumΛn₀ n₁)
      rw[this]
      apply add_eq_left.mpr
      convert tsum_zero with n
      convert mul_zero _
      apply smoothIs0
      rw[← mul_le_mul_iff_left₀ X_pos]
      rw [(by field_simp : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁)),
        (by ring : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1)), Nat.cast_add, Nat.cast_add]
      bound]

    have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
      rw[Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
      apply le_trans <| Nat.le_ceil X
      exact_mod_cast Nat.ceil_le_floor_add_one X

    have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := Nat.floor_le (by positivity)

    rw [show ψ X =
        (∑ x ∈ Finset.range n₀, Λ x) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) by
      field_simp
      simp only [add_comm _ n₀]
      rw [← Finset.sum_range_add, Nat.add_sub_of_le, Chebyshev.psi_eq_sum_Icc,
        ← Nat.range_succ_eq_Icc_zero, Nat.floor_add_one X_pos.le]
      dsimp only [n₀]
      exact Nat.ceil_le.mpr (by linarith)]

    rw [show ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
        ∑ n ∈ Finset.range n₀, Λ n by
      apply Finset.sum_congr rfl
      intro n hn
      obtain rfl|n_zero := eq_or_ne n 0
      · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
      · convert mul_one _
        apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
        simp only [Finset.mem_range, n₀] at hn
        exact Nat.lt_ceil.mp hn |>.le]
    have vonBnd1 :
      ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
      intro n hn
      have n_add_n0_le_n1: (n : ℝ) + n₀ ≤ n₁ := by
        apply le_of_lt
        rw[Finset.mem_range] at hn
        rw[← add_lt_add_iff_right (-↑n₀), add_neg_cancel_right, add_comm, ← sub_eq_neg_add]
        exact_mod_cast hn
      have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
        rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
        apply ArithmeticFunction.vonMangoldt_le_log
      have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (↑n₁) := by
        exact_mod_cast Real.log_le_log (by positivity) n_add_n0_le_n1
      have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by
        exact Real.log_le_log (by bound) (by linarith)
      exact le_imp_le_of_le_of_le inter1 inter3 inter2

    have bnd1 :
      ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
      ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
      have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) =
          (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
        rw[← Nat.cast_sub]
        · nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
          rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
          exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
        exact n₁_ge_n₀
      rw [this]
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
      apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      · dsimp only [F]
        apply smooth1BddAbove
        bound
      rw[← Nat.cast_add]
      dsimp only [F]
      apply smooth1BddBelow
      bound

    have bnd2 :
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
      have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) =
          (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
        rw[← Nat.cast_sub]
        · nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
          rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
          exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
        simp only [Nat.ceil_le, n₀]
        exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X
          X_le_floor_add_one
      rw[this]
      apply Finset.sum_le_sum
      intro n hn
      have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
        rw[Finset.mem_range] at hn
        rw [← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero,
          ← sub_eq_add_neg]
        have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
          rw [← Nat.cast_sub, Nat.cast_lt]
          · exact hn
          simp only [Nat.ceil_le, n₀]
          exact le_trans n₀_inside_le_X X_le_floor_add_one
        have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
          apply sub_le_sub_right floor_X_add_one_le_self
        exact le_of_lt (lt_of_le_of_lt' this temp)
      have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
        rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
        apply ArithmeticFunction.vonMangoldt_le_log
      apply le_trans inter1
      exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)

    clear vonBnd1

    have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
      apply Real.log_le_log (by positivity)
      have const_le_2: 1 + c₂ * ε ≤ 3 := by
        have : (3 : ℝ) = 1 + 2 := by ring
        rw[this]
        apply add_le_add_right
        rw[← mul_one 2]
        exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      rw[mul_comm]
      exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

    calc
      _ = ‖∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) -
            ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀) + Λ n₁ * F (↑n₁ / X)‖ := by
        congr 1
        ring
      _ ≤ (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
          ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
          ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ := by
        apply norm_add_le_of_le
        · apply norm_sub_le_of_le
          · apply norm_sum_le_of_le
            intro b hb
            exact norm_mul_le_of_le (by rfl) (by rfl)
          apply norm_sum_le_of_le
          intro b hb
          rfl
        exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)
      _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by
        apply add_le_add
        · apply le_trans <| add_le_add bnd1 bnd2
          rw [(by ring : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁)), add_mul]
          apply add_le_add
          · calc
              _ ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
                apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
                rw[← Real.log_mul (by positivity) (by positivity)]
                nth_rewrite 3 [mul_comm]
                exact inter1
              _ ≤ 2 * ((X * ε * (c₂ + c₁)) * Real.log X) := by
                rw[two_mul, mul_add]
                bound
              _ = _ := by ring
          calc
            _ ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
              apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
              · rw [(by ring : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)))]
                apply sub_le_sub
                · apply le_trans floor_X_add_one_le_self
                  ring_nf
                  rw[add_comm, add_le_add_iff_left]
                  exact X_bound_1
                nth_rewrite 2 [mul_comm]
                exact n₀_gt
              rw[← Real.log_mul (by positivity) (by norm_num), mul_comm]
              exact Real.log_le_log (by positivity) (by linarith)
            _ = 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log 3) := by ring
            _ ≤ 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log X) := by gcongr
            _ = _ := by ring
        · apply le_trans _ inter1
          rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
          apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
          · rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
            exact le_trans ArithmeticFunction.vonMangoldt_le_log <|
              Real.log_le_log (mod_cast n₁_pos) n₁_le
          rw[Real.norm_of_nonneg <| smooth1BddBelow _ n₁_pos]
          apply smooth1BddAbove _ n₁_pos
      _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (Real.log X + (Real.log X + Real.log 3)) := by
        rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
        nth_rewrite 2 [mul_add]
        apply add_le_add_right
        nth_rewrite 1 [← one_mul (Real.log (3 * X))]
        apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
        linarith
      _ = 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
            2 * (X * ε * (3 * c₁ + c₂)) * Real.log 3 := by ring
      _ ≤ 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
            2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by gcongr
      _ = _ := by
        rw [C_eq]
        ring
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
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one

  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF

  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl

  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩

  have X_gt_zero : (0 : ℝ) < X := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith

  intro X_bound

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    · have : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw[one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
        · exact Real.log_pos (by norm_num)
        norm_num
      exact le_of_lt (gt_trans X_bound this)
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    · have : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        · rw[one_div_lt_one_div, ← one_mul (1 / 2)]
          · apply mul_lt_mul
            · norm_num
            · apply le_of_lt
              exact lt_trans (by norm_num) (Real.log_two_gt_d9)
            repeat norm_num
          · norm_num
            exact Real.log_pos (by norm_num)
          · norm_num
      exact le_of_lt (gt_trans X_bound this)
    norm_num
    exact Real.log_pos (by norm_num)

  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]

  convert SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε
    ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow
    smoothIs1 smoothIs0
