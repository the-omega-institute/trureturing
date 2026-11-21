/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualProtectedZeroPair
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualProtectedZeroPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The protected actual zeta pair contributes an exact cosine with its analytic multiplicity. -/

import D5.S3.Analytic.Asymptotics.PositiveSpectralKernel
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open PositiveSpectralKernel (expMoment)
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open scoped BigOperators Classical ComplexConjugate

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualProtectedZeroPair

private theorem occurrence_pair_hasSum {n j : ℕ} (hnj : n ≠ j) (f : ℂ → ℂ) :
    HasSum (fun k : ℕ =>
      if actualZero k = actualData.zero n ∨ actualZero k = actualData.zero j then
        f (actualZero k) else 0)
      ((actualData.multiplicity n : ℂ) * f (actualData.zero n) +
        (actualData.multiplicity j : ℂ) * f (actualData.zero j)) := by
  let s : Finset ActualZeroOccurrence :=
    ({n, j} : Finset ℕ).sigma (fun i => (Finset.univ : Finset (Fin (actualData.multiplicity i))))
  let g : ActualZeroOccurrence → ℂ := fun p =>
    if actualData.zero p.1 = actualData.zero n ∨ actualData.zero p.1 = actualData.zero j then
      f (actualData.zero p.1) else 0
  have hg : HasSum g (∑ p ∈ s, g p) := by
    apply hasSum_sum_of_ne_finset_zero
    intro p hp
    simp only [s, Finset.mem_sigma, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_univ, and_true, not_or] at hp
    have hnot : ¬ (actualData.zero p.1 = actualData.zero n ∨
        actualData.zero p.1 = actualData.zero j) := by
      rintro (hn | hj)
      · exact hp.1 (actualData.zero_injective hn)
      · exact hp.2 (actualData.zero_injective hj)
    exact if_neg hnot
  have hsum : (∑ p ∈ s, g p) =
      (actualData.multiplicity n : ℂ) * f (actualData.zero n) +
        (actualData.multiplicity j : ℂ) * f (actualData.zero j) := by
    dsimp only [s]
    rw [Finset.sum_sigma, Finset.sum_pair hnj]
    simp only [g, eq_self, true_or, or_true, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hg
  apply ((actualOccurrenceEquiv.hasSum_iff).2 hg).congr_fun
  intro k
  simp only [Function.comp_apply, g, actualZero]
  exact congrArg
    (fun d : Decidable (actualZero k = actualData.zero n ∨ actualZero k = actualData.zero j) =>
      @ite ℂ _ d (f (actualZero k)) 0)
    (Subsingleton.elim _ _)

private theorem expMoment_conj (ν : Measure ℝ) (z : ℂ) :
    expMoment ν (conj z) = conj (expMoment ν z) := by
  change (∫ x : ℝ, Complex.exp (conj z * (x : ℂ)) ∂ν) =
    conj (∫ x : ℝ, Complex.exp (z * (x : ℂ)) ∂ν)
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [← Complex.exp_conj, map_mul, Complex.conj_ofReal]

/-- In the forward-filtered Robin spectral series, every occurrence of the protected zero
and its conjugate contributes to the same real cosine. Its amplitude is positive when the
protected moment is nonzero. The measure can in particular be the compact probability filter. -/
theorem actual_protected_pair_hasSum (ν : Measure ℝ) (k₀ : ℕ)
    (hγ : 0 < (actualZero k₀).im)
    (hmoment : expMoment ν (actualZero k₀ - 1) ≠ 0) :
    let ρ := actualZero k₀
    let a := actualCoeff k₀ * expMoment ν (ρ - 1)
    let m := analyticOrderNatAt riemannZeta ρ
    let C : ℝ := 2 * (m : ℝ) * ‖a‖
    0 < C ∧ ∀ y : ℝ,
      HasSum (fun k : ℕ =>
        if actualZero k = ρ ∨ actualZero k = conj ρ then
          actualCoeff k * expMoment ν (actualZero k - 1) *
            Complex.exp ((actualZero k - 1) * (y : ℂ)) else 0)
        ((C * Real.exp ((ρ.re - 1) * y) * Real.cos (ρ.im * y + a.arg) : ℝ) : ℂ) := by
  let ρ := actualZero k₀
  let n := (actualOccurrenceEquiv k₀).1
  let a := actualCoeff k₀ * expMoment ν (ρ - 1)
  let m := analyticOrderNatAt riemannZeta ρ
  have hm : actualData.multiplicity n = m :=
    D5.S3.Weil.ZetaBridge.ClassicExplicitFormula.multiplicity_eq_zeroMult actualData n
  have hmpos : 0 < m := hm ▸ actualData.multiplicity_pos n
  have hconj : actualData.zero (actualData.conjugation n) = conj ρ :=
    actualData.zero_conjugation n
  change 0 < ρ.im at hγ
  have hne : n ≠ actualData.conjugation n := by
    intro h
    have hi := congrArg Complex.im hconj
    rw [← h, Complex.conj_im] at hi
    change ρ.im = -ρ.im at hi
    linarith
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hγ
    exact (lt_irrefl 0) hγ
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_im] at hγ
    exact (lt_irrefl 0) hγ
  have ha : a ≠ 0 :=
    mul_ne_zero (one_div_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1.symm))) hmoment
  constructor
  · exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hmpos)) (norm_pos_iff.mpr ha)
  · intro y
    let f : ℂ → ℂ := fun z =>
      (1 / (z * (1 - z))) * expMoment ν (z - 1) * Complex.exp ((z - 1) * (y : ℂ))
    have hf : f (conj ρ) = conj (f ρ) := by
      simp only [f, map_mul, map_div₀, map_one, map_sub, Complex.conj_ofReal,
        ← expMoment_conj, ← Complex.exp_conj]
    have hre : (f ρ).re =
        ‖a‖ * Real.exp ((ρ.re - 1) * y) * Real.cos (ρ.im * y + a.arg) := by
      change (a * Complex.exp ((ρ - 1) * (y : ℂ))).re = _
      simp only [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero,
        Real.cos_add]
      rw [← Complex.norm_mul_cos_arg a, ← Complex.norm_mul_sin_arg a]
      ring
    have hvalue : (m : ℂ) * (f ρ + conj (f ρ)) =
        ((2 * (m : ℝ) * ‖a‖ * Real.exp ((ρ.re - 1) * y) *
          Real.cos (ρ.im * y + a.arg) : ℝ) : ℂ) := by
      rw [Complex.add_conj, hre]
      push_cast
      ring
    have hs := occurrence_pair_hasSum hne f
    have hnρ : actualData.zero n = ρ := rfl
    rw [hconj, hnρ, actualData.multiplicity_conjugation, hm, hf, ← mul_add, hvalue] at hs
    exact hs

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualProtectedZeroPair
