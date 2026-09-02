/- GID: D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit
   mirror-E: none(waiver:kernel-verified-orbit-sign-identities-only)
   anchors: []
   digest: A prescribed spectral pair makes a nonreal off-line zero orbit negative. -/

import D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds

/- Library-search audit trail (2026-09-02):
   * Repository searches found no prior prescribed-pair orbit theorem.
   * The frozen orbit identity and convolution-square factorization are reused below.
   * Pinned Mathlib supplies complex norm-square algebra but no repository-specific orbit result.
-/

namespace D5.S3.Weil.ZetaBridge.PrescribedPairNegativeOrbit

open Complex
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOffLineOrbits
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open scoped ComplexConjugate

noncomputable section

/-- Prescribing opposite unit transform values makes a nonreal off-line orbit negative. -/
theorem prescribed_pair_gives_negative_zero_orbit
    (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (hIm : (Z.zero n).im ≠ 0)
    (g : WeilTestFunction)
    (hz : fourierLaplace g (Z.gamma n) = 1)
    (hcz : fourierLaplace g (conj (Z.gamma n)) = -1) :
    (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ),
      zeroSummand Z (convolutionSquare g) k).re =
        -4 * (Z.multiplicity n : ℝ) := by
  have hConjugate : Z.conjugation n ≠ n := by
    intro hfixed
    have hzero := Z.zero_conjugation n
    rw [hfixed] at hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.conj_im] at him
    apply hIm
    linarith
  rw [off_line_zero_orbit_sum_eq_four_mul_re Z g n hConjugate hOff]
  simp only [Complex.ofReal_re]
  rw [zeroSummand, fourierLaplace_convolutionSquare_complex, hz, hcz]
  norm_num

private theorem real_off_line_zero_orbit_sum_eq_two_mul
    (Z : ZeroData) (n : ℕ)
    (hReal : (Z.zero n).im = 0)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (g : WeilTestFunction) :
    (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ),
      zeroSummand Z (convolutionSquare g) k) =
        2 * zeroSummand Z (convolutionSquare g) n := by
  have hConjugate : Z.conjugation n = n := by
    apply Z.zero_injective
    rw [Z.zero_conjugation]
    apply Complex.ext
    · simp
    · simpa only [Complex.conj_im, neg_eq_self] using hReal
  have hConjugateReflection :
      Z.conjugation (Z.reflection n) = Z.reflection n := by
    have hcommute := zero_symmetries_commute Z n
    rw [hConjugate] at hcommute
    exact hcommute.symm
  have hReflection : Z.reflection n ≠ n := by
    intro hfixed
    have hzero : 1 - Z.zero n = Z.zero n := by
      calc
        1 - Z.zero n = Z.zero (Z.reflection n) := (Z.zero_reflection n).symm
        _ = Z.zero n := congrArg Z.zero hfixed
    have hre : 1 - (Z.zero n).re = (Z.zero n).re := by
      simpa using congrArg Complex.re hzero
    apply hOff
    rw [criticalAbscissa]
    linarith
  rw [hConjugate, hConjugateReflection]
  have hset :
      ({n, Z.reflection n, n, Z.reflection n} : Finset ℕ) =
        {n, Z.reflection n} := by
    ext k
    simp
  rw [hset]
  have hnmem : n ∉ ({Z.reflection n} : Finset ℕ) := by
    simpa using Ne.symm hReflection
  rw [Finset.sum_insert hnmem, Finset.sum_singleton,
    zeroSummand_reflection]
  ring

/-- A real off-line zero has a two-point orbit with nonnegative norm-square value. -/
theorem real_off_line_zero_orbit_sum_re
    (Z : ZeroData) (n : ℕ)
    (hReal : (Z.zero n).im = 0)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (g : WeilTestFunction) :
    (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ),
      zeroSummand Z (convolutionSquare g) k).re =
        2 * (Z.multiplicity n : ℝ) *
          Complex.normSq (fourierLaplace g (Z.gamma n)) := by
  rw [real_off_line_zero_orbit_sum_eq_two_mul Z n hReal hOff g]
  rw [zeroSummand, fourierLaplace_convolutionSquare_complex]
  have hConjugate : Z.conjugation n = n := by
    apply Z.zero_injective
    rw [Z.zero_conjugation]
    apply Complex.ext
    · simp
    · simpa only [Complex.conj_im, neg_eq_self] using hReal
  have hgamma := Z.gamma_conjugation n
  rw [hConjugate] at hgamma
  have hgammaConj : conj (Z.gamma n) = -Z.gamma n := by
    simpa using (congrArg Neg.neg hgamma).symm
  rw [hgammaConj, fourierLaplace_neg]
  rw [show fourierLaplace g (Z.gamma n) * conj (fourierLaplace g (Z.gamma n)) =
      (Complex.normSq (fourierLaplace g (Z.gamma n)) : ℂ) by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]]
  norm_num
  ring

/-- Opposite prescribed values are impossible when the zero is real. -/
theorem prescribed_pair_impossible_for_real_zero
    (Z : ZeroData) (n : ℕ)
    (hReal : (Z.zero n).im = 0)
    (g : WeilTestFunction)
    (hz : fourierLaplace g (Z.gamma n) = 1)
    (hcz : fourierLaplace g (conj (Z.gamma n)) = -1) : False := by
  have hConjugate : Z.conjugation n = n := by
    apply Z.zero_injective
    rw [Z.zero_conjugation]
    apply Complex.ext
    · simp
    · simpa only [Complex.conj_im, neg_eq_self] using hReal
  have hgamma := Z.gamma_conjugation n
  rw [hConjugate] at hgamma
  have hgammaConj : conj (Z.gamma n) = -Z.gamma n := by
    simpa using (congrArg Neg.neg hgamma).symm
  rw [hgammaConj, fourierLaplace_neg, hz] at hcz
  norm_num at hcz

#print axioms prescribed_pair_gives_negative_zero_orbit
#print axioms real_off_line_zero_orbit_sum_re
#print axioms prescribed_pair_impossible_for_real_zero

-- These checked terms expose the exact conditional hypothesis bundles used above.
example (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa)
    (hIm : (Z.zero n).im ≠ 0)
    (g : WeilTestFunction)
    (hz : fourierLaplace g (Z.gamma n) = 1)
    (hcz : fourierLaplace g (conj (Z.gamma n)) = -1) :
    (Z.zero n).re ≠ criticalAbscissa ∧
      (Z.zero n).im ≠ 0 ∧
      fourierLaplace g (Z.gamma n) = 1 ∧
      fourierLaplace g (conj (Z.gamma n)) = -1 :=
  ⟨hOff, hIm, hz, hcz⟩

example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

end

end D5.S3.Weil.ZetaBridge.PrescribedPairNegativeOrbit
