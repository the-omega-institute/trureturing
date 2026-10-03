/- GID: D5/S3/Weil/PrimeNumberTheorem/PntLongVertical
   generality: G
   mirror-B: D5/B/S3/Weil/PrimeNumberTheorem/PntLongVertical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The long vertical contour admits a uniform logarithmic-power estimate. -/

/-
Source: AlexKontorovich/PrimeNumberTheoremAnd, revision 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01.
Original file: PrimeNumberTheoremAnd/MediumPNT.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0.
Full license and upstream attribution: Library/Weil/primenumbertheoremand2026medium.md.
This file is modified from the cited source.
Retirement: replace this consumed closure with direct references when this
repository's adopted Mathlib revision contains equivalent quantified contracts.
-/

import D5.S3.Weil.PrimeNumberTheorem.PntTail

set_option lang.lemmaCmd true

open Set Function Filter Complex Real MeasureTheory ComplexConjugate
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin
local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

set_option maxHeartbeats 400000 in
theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by
  have log_pow_over_xsq_integral_bounded :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T >3, ∫ x in Ioo 3 T, (Real.log x)^n / x^2 < C := by
    have log3gt1: 1 < Real.log 3 := logt_gt_one le_rfl
    intro n
    induction n with
    | zero =>
      use 1
      constructor
      · norm_num
      · intro T hT
        simp only [pow_zero]
        have h1 :(0 ≤ (-2) ∨ (-2) ≠ (-1) ∧ 0 ∉ Set.uIcc 3 T) := by
          right
          constructor
          · linarith
          · refine notMem_uIcc_of_lt ?_ ?_
            · exact three_pos
            · linarith
        have integral := integral_zpow h1
        ring_nf at integral

        have swap_int_kind : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), 1 / x ^ 2 = ∫ (x : ℝ) in Ioo 3 T, 1 / x ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo
        rw [← swap_int_kind]
        have change_int_power : ∫ (x : ℝ) in (3 : ℝ)..T, (1 : ℝ) / x ^ (↑ 2)
                              = ∫ (x : ℝ) in (3 : ℝ).. T, x ^ (-2 : ℤ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          simp
        rw [change_int_power, integral]
        have : T ^ (-1 : ℤ) > 0 := by
          refine zpow_pos ?_ (-1)
          linarith
        linarith
    | succ d ih =>
      obtain ⟨Cd, Cdpos, IH⟩ := ih
      use ((Real.log 3)^(d+1) / 3) + (d+1) * Cd
      constructor
      · have logpowpos : (Real.log 3) ^ (d + 1) > 0 := by
          refine pow_pos ?_ (d + 1)
          linarith
        have : Real.log 3 ^ (d + 1) / 3 + (↑d + 1) * Cd > 0 / 3 + 0 := by
          have term2_pos : 0 < (↑d + 1) * Cd := by
            refine (mul_pos_iff_of_pos_right Cdpos).mpr ?_
            exact Nat.cast_add_one_pos d
          refine add_lt_add ?_ term2_pos
          refine div_lt_div₀ logpowpos ?_ ?_ ?_
          · linarith
          · linarith
          · linarith
        ring_nf at this
        ring_nf
        exact this
      · intro T Tgt3
        let u := fun x : ℝ ↦ (Real.log x) ^ (d + 1)
        let v := fun x : ℝ ↦ -1 / x
        let u' := fun x : ℝ ↦ (d + 1 : ℝ) * (Real.log x)^d / x
        let v' := fun x : ℝ ↦ 1 / x^2

        have swap_int_type : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2
                            = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ (d + 1) / x ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        rw [← swap_int_type]

        have uIcc_is_Icc : Set.uIcc 3 T = Set.Icc 3 T := by
          exact uIcc_of_lt Tgt3

        have cont_u : ContinuousOn u (Set.uIcc 3 T) := by
          unfold u
          rw[uIcc_is_Icc]
          refine ContinuousOn.pow ?_ (d + 1)
          refine continuousOn_of_forall_continuousAt ?_
          intro x hx
          refine continuousAt_log ?_
          linarith [hx.1]

        have cont_v : ContinuousOn v (Set.uIcc 3 T) := by
          unfold v
          rw[uIcc_is_Icc]
          refine continuousOn_of_forall_continuousAt ?_
          intro x hx
          have cont2 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) (-x) := by
            refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
            · exact continuousAt_const
            · linarith [hx.1]
          have fun1 : (fun (x : ℝ) ↦ -1 / x) = (fun (x : ℝ) ↦ 1 / (-x)) := by
            ext x
            ring_nf
          rw [fun1]
          exact ContinuousAt.comp cont2 (HasDerivAt.neg (hasDerivAt_id x)).continuousAt

        have deriv_u :
            (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt u (u' x) x) := by
          intro x hx
          have min3t : min 3 T = 3 := by
            exact min_eq_left_of_lt Tgt3
          have max3t : max 3 T = T := by
            exact max_eq_right_of_lt Tgt3
          rw[min3t, max3t] at hx
          unfold u u'
          have xne0 : x ≠ 0 := by linarith [hx.1]
          have deriv2 := (Real.hasDerivAt_log xne0).pow (d + 1)
          have fun2 : (↑d + 1) * Real.log x ^ d / x =  (↑d + 1) * Real.log x ^ d * x⁻¹:= by
            exact rfl
          rw [fun2]
          convert! deriv2 using 1
          rw [Nat.add_sub_cancel,
            Nat.cast_add, Nat.cast_one]

        have deriv_v : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt v (v' x) x) := by
          intro x hx
          have min3t : min 3 T = 3 := by
            exact min_eq_left_of_lt Tgt3
          have max3t : max 3 T = T := by
            exact max_eq_right_of_lt Tgt3
          rw[min3t, max3t] at hx
          have xne0 : x ≠ 0 := by linarith [hx.1]
          unfold v v'
          have deriv1 := hasDerivAt_inv xne0
          have fun1 : (fun (x : ℝ) ↦ x⁻¹) = (fun (x : ℝ) ↦ 1 / x) := by
            ext x
            exact inv_eq_one_div x
          rw [fun1] at deriv1
          have fun2 : -(x ^ 2)⁻¹ = - 1 / x ^ 2 := by
            field_simp
          rw [fun2] at deriv1
          convert! HasDerivAt.neg deriv1 using 1
          · ext x
            rw [neg_eq_neg_one_mul]
            field_simp
            simp
          · field_simp

        have cont_u' : ContinuousOn u' (Set.uIcc 3 T) := by
          rw[uIcc_is_Icc]
          unfold u'
          refine ContinuousOn.div₀ ?_ ?_ ?_
          · refine ContinuousOn.mul ?_ ?_
            · exact continuousOn_const
            · refine ContinuousOn.pow ?_ d
              refine continuousOn_of_forall_continuousAt ?_
              intro x hx
              refine continuousAt_log ?_
              linarith [hx.1]
          · exact continuousOn_id' (Icc 3 T)
          · intro x hx
            linarith [hx.1]

        have cont_v' : ContinuousOn v' (Set.uIcc 3 T) := by
          rw[uIcc_is_Icc]
          unfold v'
          refine ContinuousOn.div₀ ?_ ?_ ?_
          · exact continuousOn_const
          · exact continuousOn_pow 2
          · intro x hx
            refine pow_ne_zero 2 ?_
            linarith [hx.1]

        have int_u': IntervalIntegrable u' MeasureTheory.volume 3 T := by
          exact ContinuousOn.intervalIntegrable cont_u'

        have int_v': IntervalIntegrable v' MeasureTheory.volume 3 T := by
          exact ContinuousOn.intervalIntegrable cont_v'

        have IBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt cont_u cont_v deriv_u deriv_v int_u' int_v'

        unfold u u' v v' at IBP

        have int1 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) * (1 / x ^ 2)
                  = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2 := by
            refine intervalIntegral.integral_congr ?_
            intro x hx
            field_simp

        rw[int1] at IBP
        rw[IBP]

        have int2 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                  = -(↑d + 1) * ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2 := by
          have : ∀ x, (↑d + 1) * Real.log x ^ d / x * (-1 / x)
           = -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
            intro x
            field_simp
          have : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                  = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
            exact intervalIntegral.integral_congr fun ⦃x⦄ a ↦ this x
          rw [this,
            ←intervalIntegral.integral_const_mul]

          ring_nf

        rw[int2]

        have int3 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2
                  = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        rw[int3]

        have IHbound : ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := by
          exact IH T Tgt3

        ring_nf
        have bound2 : (Real.log T * Real.log T ^ d * T⁻¹) ≥ 0 := by
          have logTpos : Real.log T ≥ 0 := by
            refine log_nonneg ?_
            linarith
          apply mul_nonneg
          · apply mul_nonneg
            · exact logTpos
            · exact pow_nonneg logTpos d
          · field_simp
            simp
        let S := Real.log T * Real.log T ^ d * T⁻¹
        have : (-(Real.log T * Real.log T ^ d * T⁻¹) + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                  ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
                ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 = (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                  ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
                ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
          unfold S
          rfl
        rw [this]

        have GetRidOfS : (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3)
                        + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                        + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2
                        ≤ ( Real.log 3 * Real.log 3 ^ d * (1 / 3)
                        + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                        + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
          linarith
        apply lt_of_le_of_lt GetRidOfS
        rw [add_assoc]

        have bound4 : ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := IHbound

        have bound5 : ↑d * ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 ≤ ↑d * Cd := by
          apply (mul_le_mul_of_nonneg_left bound4.le)
          exact Nat.cast_nonneg d

        rw[add_assoc]
        apply add_lt_add_right
        field_simp
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
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded 9
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have Xpos := zero_lt_three.trans Xgt3
  have Tgt3' : -T < -3 := neg_lt_neg_iff.mpr Tgt3

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      exact ht.2.trans (by norm_num)
    rw [← Set.neg_mem_Ioo_iff, mem_Ioo] at ht
    rwa [this]

  have logt9gt1_bounds :
      ∀ t, t ∈ Set.Icc (-T) (-3) → Real.log |t| ^ 9 > 1 := by
    intro t ht
    refine one_lt_pow₀ (logt_gt_one ?_) ?_
    · have : |t| = -t := by
        refine abs_of_neg ?_
        exact ht.2.trans_lt (by norm_num)
      rw [this, le_neg]
      exact ht.2
    · norm_num

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h9 : 9 ≠ 0 := by norm_num
    refine div_lt_div_of_pos_left hA.1 ?_ ?_
    · exact zero_lt_one.trans <| one_lt_pow₀ (logt_gt_one ht.1.le) h9
    · have h1 := log_lt_log (zero_lt_three.trans ht.1) ht.2
      have h2 := logt_gt_one ht.1.le
      have h3 : 0 ≤ Real.log |t| := zero_le_one.trans h2.le
      exact pow_lt_pow_left₀ h1 h3 h9

  have AoverlogT9in0half: A / Real.log T ^ 9 ∈ Ioo 0 (1/2) := by
    have logT9gt1 : 1 < Real.log T ^ 9 := by
      have logt_gt_one : 1 < Real.log T := logt_gt_one Tgt3.le
      refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logt_gt_one
      · exact zero_le_one.trans logt_gt_one.le
      · norm_num
    have logT9pos := zero_lt_one.trans logT9gt1
    constructor
    · exact div_pos hA.1 logT9pos
    · rw [div_lt_comm₀ logT9pos one_half_pos, div_lt_iff₀' one_half_pos]
      apply hA.2.trans_lt
      rwa [lt_mul_iff_one_lt_right one_half_pos]

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    linarith[AoverlogT9in0half.1]

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    linarith[AoverlogT9in0half.2]

  have quotient_bound :
      ∀ t ∈ Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9 / t ^ 2 := by
    intro t ht
    have loght := logt9gt1_bounds t (Ioo_subset_Icc_self ht)
    have logpos : Real.log |t| ^ 9 > 0 := zero_lt_one.trans loght
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := (le_add_iff_nonneg_left _).mpr <| sq_nonneg σ₁
    have denom_pos : 0 < t ^ 2 := by
      apply sq_pos_of_ne_zero
      rintro rfl
      norm_num [mem_Ioo] at ht
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) denom_pos
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have MellinBound : ∀ (t : ℝ),
      ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ₁ + t * I)‖ ≤
        CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    refine CMhyp σ₁ σ₁pos _ ?_ ?_ _ εgt0 εlt1 <;> simp [σ₁lt1.le.trans one_le_two]

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    apply hCζ
    · exact tbounds.1
    · unfold σ₁
      rw [mem_Ici, sub_le_sub_iff_left]
      exact (Aoverlogt9gtAoverlogT9_bounds t tbounds).le

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have bound_integral : ∀ t ∈ Ioo (-T) (-3), ‖f t‖ ≤ g t := by
    intro t ht
    unfold f

    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
        simp [norm_cpow_eq_rpow_re_of_pos Xpos]
      obtain ⟨ht_gt3, ht_ltT⟩ := t_bounds _ ht
      have logtgt1 : 1 < Real.log |t| := logt_gt_one ht_gt3.le
      have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
      have h𝓜 := MellinBound t
      rw[Xσ_bound]
      gcongr

    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f :
      ∫ (t : ℝ) in (-T)..(-3),
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑X ^ (↑σ₁ + ↑t * I) =
      ∫ (t : ℝ) in (-T)..(-3), f t := by
    simp only [f]
  rw[int_with_f]

  apply (norm_mul_le _ _).trans
  rw [Complex.norm_mul, Complex.norm_I, one_mul]

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ ≤ ‖∫ (t : ℝ) in (-T)..(-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · simp only [one_div, norm_inv]
      apply inv_le_one_of_one_le₀
      simp only [Complex.norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs, pi_nonneg,
        abs_of_nonneg, norm_I, mul_one]
      apply one_le_mul_of_one_le_of_one_le one_le_two
      exact le_trans (by norm_num) pi_gt_three.le
  apply le_trans this

  apply le_trans (intervalIntegral.norm_integral_le_integral_norm Tgt3'.le)

  have ne_zero_of_mem_uIcc (x) (hx : x ∈ uIcc (-T) (-3)) : x ≠ 0 := by
    rintro rfl
    norm_num [mem_uIcc] at hx
    linarith

  have cont1 : ContinuousOn (fun t ↦ Real.log |t| ^ 9) (uIcc (-T) (-3)) :=
    _root_.continuous_abs.continuousOn.log
      (fun x hx => abs_ne_zero.mpr <| ne_zero_of_mem_uIcc x hx) |>.pow 9

  have g_cont : ContinuousOn g (uIcc (-T) (-3)) := by
    unfold g
    refine .mul ?_ continuousOn_const
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_const.mul cont1
    · fun_prop
    · intro x hx
      apply mul_ne_zero εgt0.ne'
      have : 0 < σ₁ ^ 2 + x ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos σ₁pos) (sq_nonneg x)
      simp only [Complex.sq_norm, normSq_add_mul_I, ne_eq, this.ne', not_false_eq_true]

  have int_normf_le_int_g: ∫ (t : ℝ) in (-T)..(-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in (-T)..(-3), g ↑t := by
    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · exact intervalIntegral.integral_mono_on_of_le_Ioo
        Tgt3'.le h_int g_cont.intervalIntegrable bound_integral
    · rw [intervalIntegral.integral_undef h_int]
      apply intervalIntegral.integral_nonneg Tgt3'.le
      intro t ht
      unfold g
      have := logt9gt1_bounds t ht
      positivity

  apply le_trans int_normf_le_int_g
  unfold g

  simp only [σ₁]

  have : X ^ (1 - A / Real.log T ^ 9) = X * X ^ (- A / Real.log T ^ 9) := by
    rw [sub_eq_add_neg, Real.rpow_add Xpos, Real.rpow_one, neg_div]

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in (-T)..(-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]

    have bound : ∫ t in (-T)..(-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      simp_rw [Complex.sq_norm, normSq_add_mul_I]

      have : ∫ t in (-T)..(-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in (-T)..(-3), Real.log |t| ^ 9 /  t ^ 2 := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo Tgt3'.le ?_ ?_ ?_
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' _
            · intro t ht
              have h1 : 0 < t ^ 2 := pow_two_pos_of_ne_zero (ne_zero_of_mem_uIcc t ht)
              have h2 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              exact (add_pos_of_pos_of_nonneg h2 h1.le).ne'
          apply cont.intervalIntegrable
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.uIcc (-T) (-3)) := by
            refine ContinuousOn.div cont1 ?_ ?_
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' _
            · intro t ht
              exact pow_ne_zero 2 (ne_zero_of_mem_uIcc t ht)
          apply cont.intervalIntegrable
        · intro x hx
          exact quotient_bound x hx
      apply le_trans this
      rw [← intervalIntegral.integral_comp_neg]
      simp only [abs_neg, log_abs, even_two, Even.neg_pow]
      rw [intervalIntegral.integral_of_le Tgt3.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact (Cinthyp T Tgt3).le
    rw [mul_comm,
      ← mul_div_assoc, mul_one]

    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in (-T)..(-3), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ^ 9))
  = Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     simp only [log_abs]
     rw [← intervalIntegral.integral_const_mul]
     apply intervalIntegral.integral_congr
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T ^ 9)) * ∫ (t : ℝ) in (-T)..(-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T ^ 9)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · positivity

  apply le_trans this
  ring_nf
  field_simp
  simp
