/- COMPLETE SOURCE OVERLAY ONLY — UNCOMPILED.
   Original section479, original 100/500-scale interval, complete inclusive U.
   The current natural Gaussian4590 owner and reviewed F3/F5 repairs are
   integrated. The pinned four whole-formula modules remain source-only API
   dependencies. No compilation, kernel acceptance, registration or RH claim. -/
import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Weil.ZeroData.ActualGaussianDirectTail
import D5.S3.Arith.Robin.OriginalGaussianIntegralBudgets
import D5.S3.Arith.Robin.MangoldtPeakExponentialBudget
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ActualGaussianZeroSum
open D5.S3.Weil.ZeroData.ActualGaussianDirectTail
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Arith.Robin.OriginalGaussianIntegralBudgets
open D5.S3.Arith.Robin.ActualGaussianEnvelopeMassBudget
open D5.S3.Weil.Mertens.IntegratedExplicit

namespace D5.S3.Arith.Robin.OriginalPositiveUPeak

/-- Connect the two literal occurrence sums, then pay the ENTIRE correction.
The equality is proved by unfolding the actual coefficients, never assumed.
This helper is consumed on the proof path to the original existential. -/
private theorem actual_H_re_le_U {y : ℝ} (hy : 0 < y) :
    (H y).re ≤ U (Real.exp y) := by
  have hformula : H y =
      ((U (Real.exp y) - Real.log (2 * Real.pi) + trivialT y : ℝ) : ℂ) := by
    simpa only [H, actualH, actualCoeff] using actual_integrated_explicit_formula hy
  have hre := congrArg Complex.re hformula
  simp only [Complex.ofReal_re] at hre
  have hmass : trivialT y ≤ 1 - Real.log 2 := trivialT_le_mass hy.le
  have hlogtwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogpi : 1 < Real.log (2 * Real.pi) := by
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < 2 * Real.pi)).2
    exact Real.exp_one_lt_three.trans (by linarith [Real.pi_gt_three])
  linarith

/-- Signed localization BEFORE replacing the signed debit by its norm.
All four integrals below are integrals of genuinely integrable functions.
The term subtracted is integral(f*v), not integral(|f|*v). The proof reuses
the sealed GaussianSignedLocalization pointwise/indicator argument, stopping
before its last absolute-value relaxation. This stronger helper is consumed. -/
private theorem signed_localization_debit
    (f k v B : ℝ → ℝ) (J : Set ℝ) (hJ : MeasurableSet J)
    (hk : ∀ y, |k y| ≤ v y)
    (hB : ∀ y ∈ J, 0 ≤ B y) (hfB : ∀ y ∈ J, f y ≤ B y)
    (hfk : Integrable (fun y => f y * k y))
    (hfv : Integrable (fun y => f y * v y))
    (hBv : Integrable (fun y => B y * v y))
    (hav : Integrable (fun y => |f y| * v y)) :
    (∫ y : ℝ, f y * k y) ≤
      2 * (∫ y in J, B y * v y) +
        2 * (∫ y in Jᶜ, |f y| * v y) - ∫ y : ℝ, f y * v y := by
  have hcentral : Integrable (J.indicator (fun y => 2 * (B y * v y))) :=
    (hBv.const_mul 2).indicator hJ
  have hexterior : Integrable (Jᶜ.indicator (fun y => 2 * (|f y| * v y))) :=
    (hav.const_mul 2).indicator hJ.compl
  have hpoint (y : ℝ) : f y * k y ≤
      J.indicator (fun x => 2 * (B x * v x)) y +
        Jᶜ.indicator (fun x => 2 * (|f x| * v x)) y - f y * v y := by
    obtain ⟨hkm, hkp⟩ := abs_le.mp (hk y)
    have hplus : 0 ≤ k y + v y := by linarith
    by_cases hy : y ∈ J
    · rw [Set.indicator_of_mem hy,
        Set.indicator_of_notMem (show y ∉ Jᶜ from fun h => h hy), add_zero]
      have hmul := mul_le_mul_of_nonneg_right (hfB y hy) hplus
      have hbudget := mul_le_mul_of_nonneg_left hkp (hB y hy)
      nlinarith
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_mem (show y ∈ Jᶜ from hy), zero_add]
      have hmul := mul_le_mul_of_nonneg_right (le_abs_self (f y)) hplus
      have hbudget := mul_le_mul_of_nonneg_left hkp (abs_nonneg (f y))
      nlinarith
  have hle := integral_mono hfk ((hcentral.add hexterior).sub hfv) hpoint
  have hle' : (∫ x : ℝ, f x * k x) ≤
      ∫ x : ℝ,
        (J.indicator (fun y => 2 * (B y * v y)) x +
            Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x) - f x * v x := by
    simpa only [Pi.add_apply, Pi.sub_apply] using hle
  have hsub :
      (∫ x : ℝ,
          J.indicator (fun y => 2 * (B y * v y)) x +
            Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x - f x * v x) =
        (∫ x : ℝ,
          J.indicator (fun y => 2 * (B y * v y)) x +
            Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x) -
          ∫ x : ℝ, f x * v x := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      (integral_sub (hcentral.add hexterior) hfv)
  calc
    (∫ x : ℝ, f x * k x) ≤
        ∫ x : ℝ,
          (J.indicator (fun y => 2 * (B y * v y)) x +
              Jᶜ.indicator (fun y => 2 * (|f y| * v y)) x) - f x * v x := hle'
    _ = (2 * (∫ y in J, B y * v y) +
          2 * (∫ y in Jᶜ, |f y| * v y)) - ∫ y : ℝ, f y * v y := by
      rw [hsub, integral_add hcentral hexterior,
        integral_indicator hJ, integral_indicator hJ.compl,
        integral_const_mul, integral_const_mul]

/-- All four original F5 constants are consumed, on their exact domains.
The interval bound is an internal consequence of the no-peak contradiction,
not an additional hypothesis of the final actual-zero theorem. -/
private theorem full_E_upper_of_central_bound
    (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ)
    (hH : ∀ y ∈ Icc (4 * m) (28 * m), (H y).re ≤ b y) :
    (E m γ).re ≤ 2000 * m * (γ + 10) ^ 2 * Real.exp (33 * m / 4) := by
  have hmpos : 0 < m := by linarith
  have hHK := H_real_K_product_integrable m γ hmpos
  have hHv := H_real_V_product_integrable m γ hmpos
  have hbv := bv_integrable m γ hmpos
  have hav := abs_Hv_integrable m γ hmpos
  have hdom (y : ℝ) : |gaussianK m γ y| ≤ gaussianV m γ y := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (gaussian_kernel_domination m γ y hm).1
  have hbJ (y : ℝ) (hy : y ∈ Icc (4 * m) (28 * m)) : 0 ≤ b y := by
    have hy0 : 0 ≤ y := by linarith [hy.1]
    dsimp only [b]
    positivity
  have hdebit := signed_localization_debit (fun y => (H y).re)
    (gaussianK m γ) (gaussianV m γ) b (Icc (4 * m) (28 * m))
    measurableSet_Icc hdom hbJ hH hHK hHv hbv hav
  have hE : (∫ y : ℝ, (H y).re * gaussianK m γ y) = (E m γ).re := by
    rw [actual_signed_K_exchange m γ hmpos]
    unfold E summand
    congr 1
    apply tsum_congr
    intro k
    congr 1
    ring
  rw [hE] at hdebit

  -- Enlarge ONLY the central positive majorant; pay the null endpoint.
  have hsubset : Icc (4 * m) (28 * m) ⊆ Ici (0 : ℝ) := by
    intro y hy
    change 0 ≤ y
    linarith [hy.1]
  have hposbv : 0 ≤ᵐ[volume.restrict (Ici (0 : ℝ))]
      (fun y => b y * gaussianV m γ y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    have hy0 : 0 ≤ y := hy
    exact mul_nonneg (by dsimp only [b]; positivity) (V_nonneg m γ y)
  have hcentral : (∫ y in Icc (4 * m) (28 * m), b y * gaussianV m γ y) ≤
      ∫ y in Ioi 0, b y * gaussianV m γ y := by
    calc
      _ ≤ ∫ y in Ici 0, b y * gaussianV m γ y :=
        setIntegral_mono_set hbv.integrableOn hposbv
          (ae_of_all volume fun y hy => hsubset hy)
      _ = _ := central_zero_endpoint m γ

  -- Exact disjoint complement; both closed endpoints stay in J.
  have hout : (∫ y in (Icc (4 * m) (28 * m))ᶜ,
      |(H y).re| * gaussianV m γ y) =
      (∫ y in Ici 0 \ Icc (4 * m) (28 * m), |(H y).re| * gaussianV m γ y) +
        ∫ y in Iio 0, |(H y).re| * gaussianV m γ y := by
    rw [exterior_decomposition m hm]
    exact setIntegral_union (exterior_disjoint m) measurableSet_Iio
      hav.integrableOn hav.integrableOn
  rw [hout] at hdebit
  have hwhole := full_Hv_original m γ hm hγ
  have hcentralBudget := central_original m γ hm hγ
  have hnonnegative := nonnegative_exterior_original m γ hm hγ
  have hnegative := negative_exterior_original m γ hm hγ
  have hcentralPaid := hcentral.trans hcentralBudget
  have hdebitPaid :=
    (neg_le_abs (∫ y : ℝ, (H y).re * gaussianV m γ y)).trans hwhole
  have hupper : (E m γ).re ≤
      600 * m * (γ + 10) ^ 2 * Real.exp (33 * m / 4) +
        24 * (γ + 10) ^ 2 * Real.exp (9 * m / 2) +
        16 * (γ + 10) ^ 2 * Real.exp (-32 * m) +
        1000 * (γ + 10) ^ 2 * Real.exp (-83 * m) := by
    nlinarith only [hdebit, hcentralPaid, hnonnegative, hnegative, hdebitPaid]
  have absorb (t : ℝ) (ht : t ≤ 33 * m / 4) :
      (γ + 10) ^ 2 * Real.exp t ≤
        m * (γ + 10) ^ 2 * Real.exp (33 * m / 4) := by
    calc
      _ ≤ (γ + 10) ^ 2 * Real.exp (33 * m / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht) (sq_nonneg (γ + 10))
      _ = 1 * ((γ + 10) ^ 2 * Real.exp (33 * m / 4)) := by ring
      _ ≤ m * ((γ + 10) ^ 2 * Real.exp (33 * m / 4)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by ring
  have hposAbsorb := absorb (9 * m / 2) (by linarith)
  have hnegAbsorb := absorb (-32 * m) (by linarith)
  have hwholeAbsorb := absorb (-83 * m) (by linarith)
  have hscale : 0 ≤ m * (γ + 10) ^ 2 * Real.exp (33 * m / 4) := by positivity
  -- 600 + 24 + 16 + 1000 = 1640 < 2000.
  nlinarith only [hupper, hposAbsorb, hnegAbsorb, hwholeAbsorb, hscale]

/-- Original positive complete-U witness. The ONLY premises are an ACTUAL
nontrivial zero and its stated beta/gamma inequalities. Original constants
100, 500, 4, 28 and the inclusive complete Mangoldt U are unchanged.
This is a complete proof-script candidate, not a native acceptance receipt. -/
theorem original_positive_U_peak (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hγ : 0 < ρ.im) :
    let δ := ρ.re - 1 / 2
    let D := ρ.im + 10
    let m₀ := 100 * D ^ 2 / δ ^ 2
    let m₁ := 500 * D ^ 4 / δ ^ 2
    ∃ A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)),
      Real.sqrt A * (4 * Real.log A + 9) < U A := by
  classical
  let δ : ℝ := ρ.re - 1 / 2
  let D : ℝ := ρ.im + 10
  let m₀ : ℝ := 100 * D ^ 2 / δ ^ 2
  let m₁ : ℝ := 500 * D ^ 4 / δ ^ 2
  let a : ℝ := ρ.re ^ 2 + 16 * ρ.re
  change ∃ A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)),
    Real.sqrt A * (4 * Real.log A + 9) < U A
  have hheight : 10 < ρ.im := by
    simpa only [abs_of_pos hγ] using actual_height_gt_ten ρ hρ
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hδhalf : δ < 1 / 2 := by dsimp only [δ]; linarith [hρ.2.2]
  have hD : 20 < D := by dsimp only [D]; linarith
  obtain ⟨m, hmlo, hmhi, hm, hElower⟩ := full_E_original_time ρ hρ hβ hγ
  change m₀ ≤ m at hmlo
  change m ≤ m₁ at hmhi
  change Real.exp (a * m) / 2 ≤ (E m ρ.im).re at hElower
  have hmpos : 0 < m := by linarith
  by_contra hnone
  have hU (A : ℝ) (hA : A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁))) :
      U A ≤ Real.sqrt A * (4 * Real.log A + 9) := by
    apply le_of_not_gt
    intro hp
    exact hnone ⟨A, hA, hp⟩
  have hH (y : ℝ) (hy : y ∈ Icc (4 * m) (28 * m)) : (H y).re ≤ b y := by
    have hypos : 0 < y := by linarith [hy.1]
    have hA : Real.exp y ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)) := by
      constructor
      · apply Real.exp_le_exp.mpr
        linarith [hy.1]
      · apply Real.exp_le_exp.mpr
        linarith [hy.2]
    have hsqrt : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
      apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos (y / 2))).2
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (H y).re ≤ U (Real.exp y) := actual_H_re_le_U hypos
      _ ≤ Real.sqrt (Real.exp y) * (4 * Real.log (Real.exp y) + 9) := hU _ hA
      _ = (4 * y + 9) * Real.exp (y / 2) := by rw [hsqrt, Real.log_exp]; ring
      _ ≤ b y := by dsimp only [b]; nlinarith [Real.exp_pos (y / 2)]
  have hEupper : (E m ρ.im).re ≤ 2000 * m * D ^ 2 * Real.exp (33 * m / 4) :=
    full_E_upper_of_central_bound m ρ.im hm hheight hH
  have hTaylor :=
    D5.S3.Arith.Robin.MangoldtPeakExponentialBudget.exponential_dominates
      δ D m hδ (by linarith : 0 < D) hmlo
  have ha : a = 33 / 4 + 17 * δ + δ ^ 2 := by dsimp only [a, δ]; ring
  have haTime : 17 * δ * m + 33 * m / 4 ≤ a * m := by
    rw [ha]
    nlinarith [mul_nonneg (sq_nonneg δ) hmpos.le]
  have hstrict : 4000 * m * D ^ 2 * Real.exp (33 * m / 4) < Real.exp (a * m) := by
    calc
      _ < Real.exp (17 * δ * m) * Real.exp (33 * m / 4) :=
        mul_lt_mul_of_pos_right hTaylor (Real.exp_pos _)
      _ = Real.exp (17 * δ * m + 33 * m / 4) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (a * m) := Real.exp_le_exp.mpr haTime
  nlinarith only [hElower, hEupper, hstrict]

end D5.S3.Arith.Robin.OriginalPositiveUPeak
end
