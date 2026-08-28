/- GID: D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PrimeJumpDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose the finite prime-power term into coherent mass and translation energy. -/

import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

namespace D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition

open MeasureTheory Set
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open scoped ArithmeticFunction ComplexConjugate

noncomputable section

/-- Prime powers visible through a convolution square supported in `[-2L, 2L]`. -/
def activePrimePowers (L : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊Real.exp (2 * L)⌋₊).filter
    (fun n => ArithmeticFunction.vonMangoldt n ≠ 0)

/-- The critical-line von Mangoldt weight. -/
def primeWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Total coherent prime-power mass at support radius `L`. -/
def totalPrimeWeight (L : ℝ) : ℝ :=
  ∑ n ∈ activePrimePowers L, primeWeight n

/-- The finite arithmetic translation energy at support radius `L`. -/
def arithmeticJumpEnergy (L : ℝ) (f : WeilTestFunction) : ℝ :=
  ∑ n ∈ activePrimePowers L,
    primeWeight n * translationEnergy f (Real.log n)

/-- The arithmetic jump Laplacian applied to a source test function. -/
def arithmeticJumpLaplacian (L : ℝ) (f : WeilTestFunction) (y : ℝ) : ℂ :=
  ∑ n ∈ activePrimePowers L, (primeWeight n : ℂ) *
    (2 * f y - f (y - Real.log n) - f (y + Real.log n))

private theorem convolution_square_eq_weil_test (f : WeilTestFunction) :
    ((convolutionSquare f : WeilTestFunction) : ℝ → ℂ) =
      Zeta23.EF.weilTest (f : ℝ → ℂ) (f : ℝ → ℂ) := by
  rfl

private theorem integrable_normSq (f : WeilTestFunction) :
    Integrable (fun y : ℝ => Complex.normSq (f y)) := by
  exact (Complex.continuous_normSq.comp f.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp_left (by simp))

private theorem integrable_correlation (f : WeilTestFunction) (x : ℝ) :
    Integrable (fun y : ℝ => f y * conj (f (y - x))) := by
  apply Continuous.integrable_of_hasCompactSupport
  · have hf : Continuous (f : ℝ → ℂ) := f.continuous
    fun_prop
  · exact f.hasCompactSupport.mul_right

private theorem convolution_square_re (f : WeilTestFunction) (x : ℝ) :
    (convolutionSquare f x).re =
      ∫ y : ℝ, (f y * conj (f (y - x))).re := by
  rw [convolutionSquare_apply]
  exact (integral_re (integrable_correlation f x)).symm

private theorem translation_energy_eq_correlation (f : WeilTestFunction) (x : ℝ) :
    translationEnergy f x =
      2 * l2Mass f - 2 * (convolutionSquare f x).re := by
  have hNorm := integrable_normSq f
  have hShift : Integrable (fun y : ℝ => Complex.normSq (f (y - x))) := by
    simpa using hNorm.comp_sub_right x
  have hCorrRe := (integrable_correlation f x).re.const_mul 2
  rw [translationEnergy]
  simp_rw [Complex.normSq_sub]
  calc
    (∫ y : ℝ, Complex.normSq (f y) + Complex.normSq (f (y - x)) -
        2 * (f y * conj (f (y - x))).re) =
        (∫ y : ℝ, Complex.normSq (f y) + Complex.normSq (f (y - x))) -
          ∫ y : ℝ, 2 * (f y * conj (f (y - x))).re :=
      integral_sub (hNorm.add hShift) hCorrRe
    _ = ((∫ y : ℝ, Complex.normSq (f y)) +
          ∫ y : ℝ, Complex.normSq (f (y - x))) -
          2 * ∫ y : ℝ, (f y * conj (f (y - x))).re := by
      rw [integral_add hNorm hShift, integral_const_mul]
    _ = 2 * l2Mass f - 2 * (convolutionSquare f x).re := by
      rw [integral_sub_right_eq_self (fun y : ℝ => Complex.normSq (f y)) x]
      rw [← convolution_square_re]
      unfold l2Mass
      ring

private theorem convolution_square_real (f : WeilTestFunction) (x : ℝ) :
    convolutionSquare f x = ((convolutionSquare f x).re : ℂ) := by
  have hfixed : involution (convolutionSquare f) = convolutionSquare f := by
    ext z
    have hswap :
        convolutionSquare f z = ∫ t : ℝ, f (z - t) * conj (f t) := by
      rw [convolutionSquare]
      change MeasureTheory.convolution f (involution f) complexMul volume z = _
      rw [MeasureTheory.convolution_eq_swap]
      apply integral_congr_ae
      filter_upwards with t
      simp only [involution_apply]
      rw [f.even t]
      rfl
    rw [involution_apply, convolutionSquare_even, convolutionSquare_apply, ← integral_conj]
    rw [← convolutionSquare_apply, hswap]
    apply integral_congr_ae
    filter_upwards with t
    simp only [map_mul, Complex.conj_conj]
    have ht := f.even (t - z)
    simp only [neg_sub] at ht
    rw [ht]
    ring
  have hconj : conj (convolutionSquare f x) = convolutionSquare f x := by
    have hx := congrArg (fun g : WeilTestFunction => g (-x)) hfixed
    rw [involution_apply, neg_neg, convolutionSquare_even] at hx
    exact hx
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im hconj
    rw [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

private theorem prime_summand_energy (f : WeilTestFunction) (n : ℕ) :
    primeSummand (convolutionSquare f) n =
      ((2 * primeWeight n * l2Mass f -
        primeWeight n * translationEnergy f (Real.log n) : ℝ) : ℂ) := by
  have hreal := convolution_square_real f (Real.log n)
  rw [show primeSummand (convolutionSquare f) n =
      (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (convolutionSquare f (Real.log n) +
          convolutionSquare f (-Real.log n))) by
    unfold primeSummand
    rw [vonMangoldt_div_sqrt]
    push_cast
    ring]
  change (primeWeight n : ℂ) *
      (convolutionSquare f (Real.log n) +
        convolutionSquare f (-Real.log n)) = _
  rw [convolutionSquare_even, hreal]
  rw [translation_energy_eq_correlation]
  push_cast
  ring

private theorem prime_term_eq_active_sum
    (f : WeilTestFunction) (L : ℝ)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-L) L) :
    primeTerm (convolutionSquare f) =
      ∑ n ∈ activePrimePowers L, primeSummand (convolutionSquare f) n := by
  have hConvSupport :
      tsupport ((convolutionSquare f : WeilTestFunction) : ℝ → ℂ) ⊆
        Icc (-(2 * L)) (2 * L) := by
    have h := Zeta23.EF.tsupport_weilTest_subset
      (L := 2 * L) (f := (f : ℝ → ℂ)) (g := (f : ℝ → ℂ))
      (by simpa only [show -(2 * L) / 2 = -L by ring,
          show 2 * L / 2 = L by ring] using hSupport)
      (by simpa only [show -(2 * L) / 2 = -L by ring,
          show 2 * L / 2 = L by ring] using hSupport)
    simpa only [convolution_square_eq_weil_test] using h
  let S := Finset.Ioc 0 ⌊Real.exp (2 * L)⌋₊
  have hOutside : ∀ n ∉ S, primeSummand (convolutionSquare f) n = 0 := by
    intro n hn
    have hz := Zeta23.EF.prime_summand_eq_zero hConvSupport hn
    rw [show primeSummand (convolutionSquare f) n =
        (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (convolutionSquare f (Real.log n) +
            convolutionSquare f (-Real.log n))) by
      unfold primeSummand
      rw [vonMangoldt_div_sqrt]
      push_cast
      ring]
    exact hz
  unfold primeTerm
  rw [tsum_eq_sum hOutside]
  unfold activePrimePowers
  change (∑ n ∈ S, primeSummand (convolutionSquare f) n) =
    ∑ n ∈ S.filter (fun n => ArithmeticFunction.vonMangoldt n ≠ 0),
      primeSummand (convolutionSquare f) n
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hLambda : ArithmeticFunction.vonMangoldt n ≠ 0
  · simp [hLambda]
  · have hz : ArithmeticFunction.vonMangoldt n = 0 := not_ne_iff.mp hLambda
    simp [hz, primeSummand]

private theorem prime_weight_nonnegative (n : ℕ) : 0 ≤ primeWeight n := by
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

private theorem translation_energy_nonnegative (f : WeilTestFunction) (x : ℝ) :
    0 ≤ translationEnergy f x := by
  unfold translationEnergy
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

private theorem channel_form_eq_translation_energy (f : WeilTestFunction) (x : ℝ) :
    (∫ y : ℝ, conj (f y) *
      (2 * f y - f (y - x) - f (y + x))).re = translationEnergy f x := by
  have hf : Continuous (f : ℝ → ℂ) := f.continuous
  have hConjSupport : HasCompactSupport (fun y : ℝ => conj (f y)) :=
    f.hasCompactSupport.comp_left (by simp)
  have hBase : Integrable (fun y : ℝ => conj (f y) * f y) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact hConjSupport.mul_right
  have hMinus : Integrable (fun y : ℝ => conj (f y) * f (y - x)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact hConjSupport.mul_right
  have hPlus : Integrable (fun y : ℝ => conj (f y) * f (y + x)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact hConjSupport.mul_right
  have hCorr (z : ℝ) :
      (∫ y : ℝ, conj (f y) * f (y - z)).re =
        (convolutionSquare f z).re := by
    rw [show (fun y : ℝ => conj (f y) * f (y - z)) =
        fun y => conj (f y * conj (f (y - z))) by
      funext y
      simp only [map_mul, Complex.conj_conj]]
    rw [integral_conj, convolutionSquare_apply]
    simp
  have hCorrMinus := hCorr x
  have hCorrPlus :
      (∫ y : ℝ, conj (f y) * f (y + x)).re =
        (convolutionSquare f x).re := by
    have h := hCorr (-x)
    simpa only [sub_neg_eq_add, convolutionSquare_even] using h
  have hMass :
      (∫ y : ℝ, conj (f y) * f y).re = l2Mass f := by
    rw [l2Mass]
    calc
      (∫ y : ℝ, conj (f y) * f y).re =
          ∫ y : ℝ, (conj (f y) * f y).re := (integral_re hBase).symm
      _ = ∫ y : ℝ, Complex.normSq (f y) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [← Complex.normSq_eq_conj_mul_self]
        simp
  rw [show (fun y : ℝ => conj (f y) *
      (2 * f y - f (y - x) - f (y + x))) =
      fun y => 2 * (conj (f y) * f y) -
        conj (f y) * f (y - x) - conj (f y) * f (y + x) by
    funext y
    ring]
  have hIntegral :
      (∫ y : ℝ, 2 * (conj (f y) * f y) -
        conj (f y) * f (y - x) - conj (f y) * f (y + x)) =
        2 * (∫ y : ℝ, conj (f y) * f y) -
          (∫ y : ℝ, conj (f y) * f (y - x)) -
          ∫ y : ℝ, conj (f y) * f (y + x) := by
    calc
      (∫ y : ℝ, 2 * (conj (f y) * f y) -
          conj (f y) * f (y - x) - conj (f y) * f (y + x)) =
          (∫ y : ℝ, 2 * (conj (f y) * f y) - conj (f y) * f (y - x)) -
            ∫ y : ℝ, conj (f y) * f (y + x) :=
        integral_sub ((hBase.const_mul 2).sub hMinus) hPlus
      _ = ((∫ y : ℝ, 2 * (conj (f y) * f y)) -
            ∫ y : ℝ, conj (f y) * f (y - x)) -
            ∫ y : ℝ, conj (f y) * f (y + x) := by
        rw [integral_sub (hBase.const_mul 2) hMinus]
      _ = 2 * (∫ y : ℝ, conj (f y) * f y) -
            (∫ y : ℝ, conj (f y) * f (y - x)) -
            ∫ y : ℝ, conj (f y) * f (y + x) := by
        rw [integral_const_mul]
  rw [hIntegral]
  simp only [Complex.sub_re, Complex.mul_re]
  norm_num
  rw [hMass, hCorrMinus, hCorrPlus]
  rw [translation_energy_eq_correlation]
  norm_num
  ring

private theorem energy_eq_laplacian_form (L : ℝ) (f : WeilTestFunction) :
    arithmeticJumpEnergy L f =
      (∫ y : ℝ, conj (f y) * arithmeticJumpLaplacian L f y).re := by
  unfold arithmeticJumpEnergy arithmeticJumpLaplacian
  rw [show (fun y : ℝ => conj (f y) *
      ∑ n ∈ activePrimePowers L, (primeWeight n : ℂ) *
        (2 * f y - f (y - Real.log n) - f (y + Real.log n))) =
      fun y => ∑ n ∈ activePrimePowers L, (primeWeight n : ℂ) *
        (conj (f y) *
          (2 * f y - f (y - Real.log n) - f (y + Real.log n))) by
    funext y
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring]
  rw [integral_finsetSum]
  · rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, channel_form_eq_translation_energy]
  · intro n hn
    apply Integrable.const_mul
    have hf : Continuous (f : ℝ → ℂ) := f.continuous
    have hConjSupport : HasCompactSupport (fun y : ℝ => conj (f y)) :=
      f.hasCompactSupport.comp_left (by simp)
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact hConjSupport.mul_right

/-- The prime-power side is coherent mass minus arithmetic translation energy; the energy is
nonnegative and is the quadratic form of the explicitly constructed jump Laplacian. -/
theorem prime_jump_decomposition
    (f : WeilTestFunction) (L : ℝ)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-L) L) :
    (primeTerm (convolutionSquare f) =
      ((2 * totalPrimeWeight L * l2Mass f - arithmeticJumpEnergy L f : ℝ) : ℂ)) ∧
    0 ≤ arithmeticJumpEnergy L f ∧
    arithmeticJumpEnergy L f =
      (∫ y : ℝ, conj (f y) * arithmeticJumpLaplacian L f y).re := by
  have hPrime := prime_term_eq_active_sum f L hSupport
  have hDecomposition : primeTerm (convolutionSquare f) =
      ((2 * totalPrimeWeight L * l2Mass f - arithmeticJumpEnergy L f : ℝ) : ℂ) := by
    have hCoherent :
        (∑ n ∈ activePrimePowers L, 2 * primeWeight n * l2Mass f) =
          2 * totalPrimeWeight L * l2Mass f := by
      calc
        (∑ n ∈ activePrimePowers L, 2 * primeWeight n * l2Mass f) =
            ∑ n ∈ activePrimePowers L, (2 * l2Mass f) * primeWeight n := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
        _ = (2 * l2Mass f) * ∑ n ∈ activePrimePowers L, primeWeight n := by
          rw [Finset.mul_sum]
        _ = 2 * totalPrimeWeight L * l2Mass f := by
          unfold totalPrimeWeight
          ring
    rw [hPrime]
    simp_rw [prime_summand_energy]
    rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, hCoherent]
    unfold arithmeticJumpEnergy
    push_cast
    rfl
  refine ⟨hDecomposition, ?_, energy_eq_laplacian_form L f⟩
  unfold arithmeticJumpEnergy
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (prime_weight_nonnegative n) (translation_energy_nonnegative f _)

#print axioms prime_jump_decomposition

end

end D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
