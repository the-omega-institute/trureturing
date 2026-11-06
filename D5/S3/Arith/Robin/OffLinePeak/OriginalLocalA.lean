/- GID: D5/S3/Arith/Robin/OffLinePeak/OriginalLocalA
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OffLinePeak/OriginalLocalA
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: An actual off-critical zero gives the exact original local-A Robin5040 violation without JY. -/

import D5.S3.Arith.Robin.OffLinePeak.FullZeroGaussianResponse
import D5.S3.Arith.Robin.OffLinePeak.GaussianPeakLocalization
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
import D5.S3.Weil.Mertens.WeightedTailTransport

/-! This ports the exact original implication and its finite signed endpoint
bridge. Positive-peak mathematics is reused from FullZeroGaussianResponse and
GaussianPeakLocalization, not claimed as new. The consumed scalar domination
and final parameter comparison follow the verified original proof. No existence
of an off-critical zero, RH proof or full first-pairing saving is asserted.
The hypotheses are precisely an actual nontrivial zero, beta>1/2 and gamma>0.
These are analytic implications, not finite numerical certificates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Arith.Robin.PrimeFiberPropagation
open D5.S3.Arith.Robin.OffLinePeak

namespace D5.S3.Arith.Robin.OriginalLocalA

private theorem exponential_dominates (δ D m : ℝ) (hδ : 0 < δ) (hD : 0 < D)
    (hm : 100 * D ^ 2 / δ ^ 2 ≤ m) :
    4000 * m * D ^ 2 < Real.exp (17 * δ * m) := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
  have hmpos : 0 < m := (div_pos (by positivity) hδsq).trans_le hm
  have ht : 100 * D ^ 2 ≤ m * δ ^ 2 := (div_le_iff₀ hδsq).mp hm
  have hprod := mul_le_mul_of_nonneg_right ht hmpos.le
  have hstrict : 0 < m * D ^ 2 := mul_pos hmpos hDsq
  have hquad : 4000 * m * D ^ 2 < (17 * δ * m) ^ 2 / 2 := by
    nlinarith
  have he := Real.pow_div_factorial_le_exp
    (x := 17 * δ * m) (by positivity) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at he
  exact hquad.trans_le he

private theorem select_positive_peak (ρ : ℂ) (hρ : IsNontrivialZero ρ)
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
  obtain ⟨r, hr⟩ := actualData.zero_exhaustive hρ
  let k₀ := actualOccurrenceEquiv.symm ⟨r, ⟨0, actualData.multiplicity_pos r⟩⟩
  have hk₀ : actualZero k₀ = ρ := by simp [actualZero, k₀, hr]
  obtain ⟨_, c, hc, _⟩ := actual_complete_H_package
  have hstrip : ∀ k, 0 < (actualZero k).re ∧ (actualZero k).re < 1 :=
    fun k => (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
  have hlow : ∀ k, 10 < |(actualZero k).im| :=
    fun k => actual_height_gt_ten _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
  have hresponse := FullZeroGaussianResponse.full_zero_gaussian_response
    actualZero hstrip c hc hlow actual_coefficient_mass k₀
      (by simpa only [hk₀] using hβ) (by simpa only [hk₀] using hγ)
  simp only [hk₀, ← div_eq_mul_inv] at hresponse
  obtain ⟨m, hmlo, hmhi, hm, _, _, hiK, hiV, hK, hElower, hsmall, _, hkernel⟩ := hresponse
  obtain ⟨_, _, _, _, _, _, hgrowth, _⟩ :=
    ZeroCoefficientBudget.zero_coefficient_budget actualZero hstrip c hc hlow
      actual_coefficient_mass
  change m₀ ≤ m at hmlo
  change m ≤ m₁ at hmhi
  rw [← hK] at hElower
  have hmpos : 0 < m := by linarith
  by_contra hnone
  have hU (A : ℝ) (hA : A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁))) :
      U A ≤ Real.sqrt A * (4 * Real.log A + 9) := by
    apply le_of_not_gt
    intro hp
    exact hnone ⟨A, hA, hp⟩
  have hH (y : ℝ) (hy : y ∈ Icc (4 * m) (28 * m)) : ZeroCoefficientBudget.H actualZero y ≤ ((4 * y + 11) * Real.exp (y / 2)) := by
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
      ZeroCoefficientBudget.H actualZero y ≤ U (Real.exp y) := by
        have hformula := congrArg Complex.re (actual_integrated_explicit_formula hypos)
        have heq : ZeroCoefficientBudget.H actualZero y = (actualH y).re := by
          simp only [ZeroCoefficientBudget.H, ZeroCoefficientBudget.Hc,
            ZeroCoefficientBudget.coefficient, actualH, actualCoeff, one_div]
          congr 2
          funext k
          rw [mul_comm (actualZero k) (y : ℂ)]
        rw [heq]
        have hmass := trivialT_le_mass hypos.le
        have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        have hpi : 1 < Real.log (2 * Real.pi) :=
          (Real.lt_log_iff_exp_lt (by positivity)).2
            (Real.exp_one_lt_three.trans (by linarith [Real.pi_gt_three]))
        simp only [Complex.ofReal_re] at hformula
        linarith
      _ ≤ Real.sqrt (Real.exp y) * (4 * Real.log (Real.exp y) + 9) := hU _ hA
      _ = (4 * y + 9) * Real.exp (y / 2) := by rw [hsqrt, Real.log_exp]; ring
      _ ≤ ((4 * y + 11) * Real.exp (y / 2)) := by nlinarith [Real.exp_pos (y / 2)]
  have hEupper : (∫ y : ℝ, ZeroCoefficientBudget.H actualZero y *
    FullZeroGaussianResponse.kernel m (16 * m) ρ.im y) ≤ 2000 * m * D ^ 2 * Real.exp (33 * m / 4) :=
    GaussianPeakLocalization.gaussian_peak_localization
      (ZeroCoefficientBudget.H actualZero) hm hheight hiK hiV
      (fun y => (hgrowth y).2.2) hsmall hkernel hH
  have hTaylor :=
    exponential_dominates
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

/- The full signed endpoint is selected at H = log A. In particular the
   local t cutoff is paid before the global B₀ comparison. -/

theorem original_zero_robin5040_localA (ρ : ℂ) (hρ : IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) (hγ : 0 < ρ.im) :
    let δ := ρ.re - 1 / 2
    let D := ρ.im + 10
    let m₀ := 100 * D ^ 2 / δ ^ 2
    let m₁ := 500 * D ^ 4 / δ ^ 2
    let B₀ := Real.exp (4 * (28 * m₁ + 20) ^ 2)
    ∃ A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)),
      Real.sqrt A * (4 * Real.log A + 9) < U A ∧
      ∃ t ∈ Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)),
        let N := Nat.lcmUpto ⌊t⌋₊
        5040 < N ∧
        divisorRatio N > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) ∧
        (N : ℝ) ≤ Real.exp (B₀ * Real.log B₀) := by
  let δ : ℝ := ρ.re - 1 / 2
  let D : ℝ := ρ.im + 10
  let m₀ : ℝ := 100 * D ^ 2 / δ ^ 2
  let m₁ : ℝ := 500 * D ^ 4 / δ ^ 2
  let B₀ : ℝ := Real.exp (4 * (28 * m₁ + 20) ^ 2)
  change ∃ A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)),
    Real.sqrt A * (4 * Real.log A + 9) < U A ∧
    ∃ t ∈ Icc A (Real.exp (4 * (Real.log A + 20) ^ 2)),
      let N := Nat.lcmUpto ⌊t⌋₊
      5040 < N ∧
      divisorRatio N > Real.exp Real.eulerMascheroniConstant * Real.log (Real.log N) ∧
      (N : ℝ) ≤ Real.exp (B₀ * Real.log B₀)
  obtain ⟨A, hAI, hpeak⟩ := select_positive_peak ρ hρ hβ hγ
  change A ∈ Icc (Real.exp (4 * m₀)) (Real.exp (28 * m₁)) at hAI
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hδhalf : δ < 1 / 2 := by dsimp only [δ]; linarith [hρ.2.2]
  have hheight : 10 < ρ.im := by
    simpa only [abs_of_pos hγ] using actual_height_gt_ten ρ hρ
  have hD : 20 < D := by dsimp only [D]; linarith
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hδsqhi : δ ^ 2 < (1 / 4 : ℝ) := by
    have hp := mul_pos (show 0 < 1 / 2 - δ by linarith)
      (show 0 < 1 / 2 + δ by linarith)
    nlinarith only [hp]
  have hDsq : 400 < D ^ 2 := by
    have hp := mul_pos (show 0 < D - 20 by linarith)
      (show 0 < D + 20 by linarith)
    nlinarith only [hp]
  have hm₀ : 160000 < m₀ := by
    dsimp only [m₀]
    apply (lt_div_iff₀ hδsq).2
    nlinarith only [hδsqhi, hDsq]
  have hA : 10000 ≤ A := by
    have he := Real.add_one_le_exp (4 * m₀)
    linarith [hAI.1]
  have hApos : 0 < A := by linarith
  have hloglo : 4 * m₀ ≤ Real.log A := by
    have he : Real.exp (4 * m₀) ≤ Real.exp (Real.log A) := by
      simpa only [Real.exp_log hApos] using hAI.1
    exact Real.exp_le_exp.mp he
  have hlogLarge : 640000 < Real.log A := by linarith
  have hH : 20000 ≤ Real.log A := by linarith only [hlogLarge]
  have hL : 0 ≤ Real.log A := by linarith
  have hAH : A ≤ Real.exp (Real.log A) := (Real.exp_log hApos).ge
  have hratio : 4 * (Real.log A) ^ 2 / (1 + Real.log A) ≤ 4 * Real.log A := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + Real.log A)).2
    nlinarith
  have hpeak' : Real.sqrt A * (4 * (Real.log A) ^ 2 / (1 + Real.log A) + 9) < U A :=
    (mul_le_mul_of_nonneg_left (by linarith :
      4 * (Real.log A) ^ 2 / (1 + Real.log A) + 9 ≤ 4 * Real.log A + 9)
      (Real.sqrt_nonneg A)).trans_lt hpeak
  have hLay : ∀ t : ℝ, 2 ≤ t → Q t = Chebyshev.psi t / t -
      (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
        Real.log t - 1 - Real.eulerMascheroniConstant := by
    intro t ht
    exact D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
      D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable ht

  -- The third component is an actual existential, not a supplied budget.
  obtain ⟨y, hy, hEndpoint⟩ :=
    (ActualSignedGaussianEndpoint.actual_complete_signed_gaussian_endpoint
      (H := Real.log A) (A := A) hH hA hAH).2.2
  have hy0 : 0 < y := by linarith [hy.1]
  have hylog : Real.log 2 ≤ y := by
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [hb]
    linarith [hy.1]
  have hAB : A ≤ Real.exp y := hAH.trans (Real.exp_le_exp.mpr hy.1)
  have hK : IntegrableOn psiErrorKernel (Ioi (Real.exp y)) :=
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set
      (Ioi_subset_Ioi (by linarith : (1 : ℝ) ≤ Real.exp y))
  have htransport := D5.S3.Weil.Mertens.WeightedTailTransport.transport_exp hylog hK
  have hidentity :
      CountableResolvent.R y *
        (Q (Real.exp y) -
          (∫ u in Ioi (Real.exp y), psiErrorKernel u *
            QuotientIntegralBudget.weightEnvelope u) /
              QuotientIntegralBudget.weightEnvelope (Real.exp y)) =
        ∫ v in Ioi y, CountableResolvent.W v * Q (Real.exp v) := by
    simpa only [D5.S3.Weil.Mertens.WeightedTailTransport.tail,
      D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail,
      D5.S3.Weil.Mertens.WeightedTailTransport.r,
      QuotientIntegralBudget.weightEnvelope, Q] using htransport.2
  have hRpos : 0 < CountableResolvent.R y := by
    dsimp only [CountableResolvent.R]
    positivity
  have hquotient :
      (∫ v in Ioi y, CountableResolvent.W v * Q (Real.exp v)) /
          CountableResolvent.R y =
        Q (Real.exp y) -
          (∫ u in Ioi (Real.exp y), psiErrorKernel u *
            QuotientIntegralBudget.weightEnvelope u) /
              QuotientIntegralBudget.weightEnvelope (Real.exp y) := by
    change (∫ v in Ioi y,
        CountableResolvent.W v * Q (Real.exp v)) /
          CountableResolvent.R y = _
    rw [← hidentity]
    exact mul_div_cancel_left₀ _ hRpos.ne'
  have htailLower : -(1 / (2 * Real.sqrt A)) < Q (Real.exp y) -
      (∫ u in Ioi (Real.exp y), psiErrorKernel u *
        QuotientIntegralBudget.weightEnvelope u) /
          QuotientIntegralBudget.weightEnvelope (Real.exp y) := by
    rw [hquotient] at hEndpoint
    exact hEndpoint
  obtain ⟨t, ht, hN, hNb, hRobin⟩ :=
    finite_mertens_peak_of_signed_endpoint hLay hA hAB htailLower hpeak'

  let B : ℝ := Real.exp (4 * (Real.log A + 20) ^ 2)
  have hyB : Real.exp y ≤ B := Real.exp_le_exp.mpr hy.2
  have htB : t ∈ Icc A B := ⟨ht.1, ht.2.trans hyB⟩
  have hLu : Real.log A ≤ 28 * m₁ := Real.exp_le_exp.mp (by
    simpa only [Real.exp_log hApos] using hAI.2)
  have hsq : (Real.log A + 20) ^ 2 ≤ (28 * m₁ + 20) ^ 2 := by
    have hp := mul_nonneg (show 0 ≤ 28 * m₁ - Real.log A by linarith)
      (show 0 ≤ 28 * m₁ + Real.log A + 40 by linarith)
    nlinarith only [hp]
  have hBB : B ≤ B₀ := Real.exp_le_exp.mpr (by nlinarith only [hsq])
  have hBpos : 0 < B := Real.exp_pos _
  have hBlog : 0 ≤ Real.log B := by dsimp only [B]; rw [Real.log_exp]; positivity
  have hlogy : 0 ≤ Real.log (Real.exp y) := by rw [Real.log_exp]; exact hy0.le
  have hyBlog : Real.log (Real.exp y) ≤ Real.log B :=
    Real.log_le_log (Real.exp_pos _) hyB
  have hyScale : Real.exp y * Real.log (Real.exp y) ≤ B * Real.log B :=
    mul_le_mul hyB hyBlog hlogy hBpos.le
  have hglobal : B * Real.log B ≤ B₀ * Real.log B₀ :=
    mul_le_mul hBB (Real.log_le_log hBpos hBB) hBlog (Real.exp_pos _).le
  refine ⟨A, hAI, hpeak, t, htB, hN, hRobin, ?_⟩
  exact hNb.trans (Real.exp_le_exp.mpr (hyScale.trans hglobal))

end D5.S3.Arith.Robin.OriginalLocalA
end
