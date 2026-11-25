/- GID: D5/S3/Arith/Robin/PriceRecord/RobinMeshFourierRecovery
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RobinMeshFourierRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered Robin samples recover literal zeta-zero multiplicity on a closed upper line. -/

import D5.S3.Analytic.Asymptotics.GapWeightedFourier
import D5.S3.Arith.Robin.PriceRecord.RobinVanishingRelativeGap
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace

/-!
# Fourier recovery from canonical Robin samples

At a closed upper bound for the real parts of the nontrivial zeta zeros,
logarithmic gap weights recover the coefficient at the chosen complex point.
The critical-line centering is `2 * Real.sqrt 2 - 2`. The coefficient counts
each zero occurrence with its literal analytic multiplicity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology

namespace D5.S3.Arith.Robin.PriceRecord.RobinMeshFourierRecovery

open D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer (log_mesh_of_ratio_one)
open D5.S3.Arith.Robin.ActualTwoPriceDefect (strictInteger)
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)
open D5.S3.Arith.Robin.PriceRecord.RobinVanishingRelativeGap
  (actual_canonical_samples_signed_asymptotic)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum actualH)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
  (ActualZeroOccurrence actualData actualOccurrenceEquiv actualZero)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZetaBridge.ZeroDataNonemptyIffInfinite
  (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq)

private theorem demodulated_actualH (w : ℂ) (y : ℝ) :
    ((Real.exp (-w.re * y) : ℂ) * actualH y) * GapWeightedFourier.phase (-w.im) y =
      ∑' j : ℕ, actualCoeff j * Complex.exp ((y : ℂ) * (actualZero j - w)) := by
  have hw : (w.re : ℂ) + Complex.I * (w.im : ℂ) = w := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im,
        neg_zero, add_zero]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re, zero_add]
  rw [actualH, ← tsum_mul_left, ← tsum_mul_right]
  apply tsum_congr
  intro j
  simp only [GapWeightedFourier.phase, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  calc
    _ = actualCoeff j *
        (Complex.exp ((y : ℂ) * actualZero j) * Complex.exp (-(w.re : ℂ) * (y : ℂ)) *
          Complex.exp (Complex.I * -(w.im : ℂ) * (y : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      apply congrArg (fun t : ℂ => actualCoeff j * Complex.exp t)
      conv_rhs => rw [← hw]
      ring

open scoped Classical in
/-- The selected Fourier mass counts each occurrence of the zero at its exact analytic order. -/
private theorem actualZeroCoefficientFiber (w : ℂ) (hw : 0 < w.re ∧ w.re < 1) :
    (∑' k : ℕ, if actualZero k = w then actualCoeff k else 0) =
      (analyticOrderNatAt riemannZeta w : ℂ) / (w * (1 - w)) := by
  by_cases hzeta : riemannZeta w = 0
  · have hwzero : IsNontrivialZero w := ⟨hzeta, hw⟩
    obtain ⟨n, hn⟩ := actualData.zero_exhaustive hwzero
    have horder : analyticOrderNatAt riemannZeta w = actualData.multiplicity n := by
      have h := (hasZetaZeroMultiplicity_iff_analyticOrderAt_eq
        (actualData.zero_isNontrivial n)).mp (actualData.multiplicity_spec n)
      rw [hn] at h
      simp [analyticOrderNatAt, h]
    let term : ActualZeroOccurrence → ℂ := fun p =>
      if actualData.zero p.1 = w then
        1 / (actualData.zero p.1 * (1 - actualData.zero p.1))
      else 0
    have hterm : Summable term := (actualOccurrenceEquiv.summable_iff).mp (by
      refine Summable.of_norm_bounded actualCoeff_hasSum.summable.norm ?_
      intro k
      change ‖(if actualZero k = w then actualCoeff k else 0)‖ ≤ ‖actualCoeff k‖
      by_cases hk : actualZero k = w
      · simp only [ite_eq_left hk, le_refl]
      · rw [ite_eq_right hk, norm_zero]
        exact norm_nonneg _)
    calc
      _ = ∑' p : ActualZeroOccurrence, term p := actualOccurrenceEquiv.tsum_eq term
      _ = ∑' m : ℕ, ∑' i : Fin (actualData.multiplicity m), term ⟨m, i⟩ :=
        hterm.tsum_sigma
      _ = ∑' i : Fin (actualData.multiplicity n), term ⟨n, i⟩ := by
        apply tsum_eq_single n
        intro m hm
        have hmw : actualData.zero m ≠ w := fun he =>
          hm (actualData.zero_injective (he.trans hn.symm))
        simp [term, hmw]
      _ = (analyticOrderNatAt riemannZeta w : ℂ) / (w * (1 - w)) := by
        simp only [term, hn, ite_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, horder, div_eq_mul_inv, one_mul]
  · have hw1 : w ≠ 1 := by
      intro he
      simpa [he] using hw.2
    have horder : analyticOrderNatAt riemannZeta w = 0 := by
      have h := (Zeta23.WeilEF.analyticAt_riemannZeta hw1).analyticOrderAt_eq_zero.mpr hzeta
      simp [analyticOrderNatAt, h]
    have hne (k : ℕ) : actualZero k ≠ w := by
      intro hk
      apply hzeta
      have hkzero : riemannZeta (actualZero k) = 0 :=
        (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).1
      simpa only [hk] using hkzero
    simp [hne, horder]

/-- The gap-weighted Fourier average of centered strict Robin optimizer samples recovers
the negative zero coefficient, with its full analytic multiplicity. -/
theorem actual_canonical_samples_fourier_recovery (w : ℂ)
    (hhalf : 1 / 2 ≤ w.re) (hone : w.re < 1)
    (hstrip : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≤ w.re)
    {N : ℕ → ℕ} (hN : StrictMono N) (hpos : 0 < N 0)
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1)) :
    Tendsto (GapWeightedFourier.average (fun k => Real.log (N k : ℝ)) (fun k =>
      (((Real.rpow (N k : ℝ) (1 - w.re) * Real.log (N k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))) : ℝ) : ℂ) -
        ((if w.re = 1 / 2 then 2 * Real.sqrt 2 - 2 else 0 : ℝ) : ℂ)) *
      GapWeightedFourier.phase (-w.im) (Real.log (N k : ℝ)))) atTop
      (𝓝 (-(analyticOrderNatAt riemannZeta w : ℂ) / (w * (1 - w)))) := by
  let y : ℕ → ℝ := fun k => Real.log (N k : ℝ)
  let s : ℕ → ℂ := fun k =>
    ((Real.rpow (N k : ℝ) (1 - w.re) * Real.log (N k : ℝ) *
      robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))) : ℝ) : ℂ) -
      ((if w.re = 1 / 2 then 2 * Real.sqrt 2 - 2 else 0 : ℝ) : ℂ)
  have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
  obtain ⟨hy, hgap⟩ := log_mesh_of_ratio_one hx hratio
  have hm : StrictMono y := by
    intro i j hij
    exact Real.log_lt_log (Nat.cast_pos.mpr (hpos.trans_le (hN.monotone (Nat.zero_le i))))
      (Nat.cast_lt.mpr (hN hij))
  have hs : Tendsto (fun k => s k + (Real.exp (-w.re * y k) : ℂ) * actualH (y k))
      atTop (𝓝 0) := by
    refine (actual_canonical_samples_signed_asymptotic hhalf hone hstrip hN.tendsto_atTop).congr ?_
    intro k
    dsimp only [s, y]
    ring
  have he : Tendsto (fun k =>
      (s k + (Real.exp (-w.re * y k) : ℂ) * actualH (y k)) *
        GapWeightedFourier.phase (-w.im) (y k)) atTop (𝓝 0) := by
    have hphase (k : ℕ) : ‖GapWeightedFourier.phase (-w.im) (y k)‖ = 1 := by
      rw [GapWeightedFourier.phase, mul_assoc, ← Complex.ofReal_mul,
        Complex.norm_exp_I_mul_ofReal]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (tendsto_zero_iff_norm_tendsto_zero.mp hs)
    simp only [norm_mul, hphase, mul_one, le_refl]
  have ha : Summable (fun j : ℕ => ‖-actualCoeff j‖) := by
    simpa only [norm_neg] using actualCoeff_hasSum.summable.norm
  have hz (j : ℕ) : (actualZero j).re ≤ w.re :=
    hstrip _ (actualData.zero_isNontrivial (actualOccurrenceEquiv j).1)
  have ht := GapWeightedFourier.tendsto_average_closed_strip_series
    (y := y) hm hy hgap (fun j => -actualCoeff j) actualZero ha w hz he
  have hlimit :
      (∑' j : ℕ, if actualZero j = w then -actualCoeff j else 0) =
        -(analyticOrderNatAt riemannZeta w : ℂ) / (w * (1 - w)) := by
    calc
      _ = ∑' j : ℕ, -(if actualZero j = w then actualCoeff j else 0) := by
        apply tsum_congr
        intro j
        by_cases hj : actualZero j = w <;> simp [hj]
      _ = _ := by
        have hw : 0 < w.re := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
        rw [tsum_neg, actualZeroCoefficientFiber w ⟨hw, hone⟩, neg_div]
  rw [hlimit] at ht
  change Tendsto (GapWeightedFourier.average y (fun k =>
    s k * GapWeightedFourier.phase (-w.im) (y k))) atTop _
  refine ht.congr fun M => ?_
  apply congrArg (fun f : ℕ → ℂ => GapWeightedFourier.average y f M)
  funext k
  rw [add_mul, demodulated_actualH]
  simp only [neg_mul, tsum_neg]
  abel

end D5.S3.Arith.Robin.PriceRecord.RobinMeshFourierRecovery
