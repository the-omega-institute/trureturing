/- GID: D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine
   mirror-E: none(waiver:structural-closure-properties-only)
   anchors: []
   digest: Split convolution-square zero cutoffs into critical and off-line contributions. -/

import D5.S3.Weil.WeilIdentity
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity

namespace D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine

open Filter
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.WeilIdentity
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity

noncomputable section

/-- A zero has real spectral parameter exactly when it lies on the critical line. -/
theorem gamma_im_eq_zero_iff_zero_on_critical_line (Z : ZeroData) (n : ℕ) :
    (Z.gamma n).im = 0 ↔ (Z.zero n).re = criticalAbscissa := by
  have hre : (Z.zero n).re = criticalAbscissa - (Z.gamma n).im := by
    have h := congrArg Complex.re (Z.zero_eq_critical_add_I_mul_gamma n)
    simpa [sub_eq_add_neg] using h
  constructor <;> intro h <;> linarith

/-- A critical-line zero contributes a nonnegative real convolution-square summand. -/
theorem critical_line_zero_summand_real_nonnegative
    (Z : ZeroData) (g : WeilTestFunction) (n : ℕ)
    (hline : (Z.zero n).re = criticalAbscissa) :
    (zeroSummand Z (convolutionSquare g) n).im = 0 ∧
      0 ≤ (zeroSummand Z (convolutionSquare g) n).re := by
  have hgammaIm : (Z.gamma n).im = 0 :=
    (gamma_im_eq_zero_iff_zero_on_critical_line Z n).2 hline
  have hgamma : Z.gamma n = ((Z.gamma n).re : ℂ) := by
    apply Complex.ext <;> simp [hgammaIm]
  have hpositive :=
    fourierLaplace_convolutionSquare_real_nonnegative g (Z.gamma n).re
  rw [zeroSummand, hgamma]
  constructor
  · simp [hpositive.1]
  · simpa using mul_nonneg (Nat.cast_nonneg (Z.multiplicity n)) hpositive.2

/-- The critical-line part of every finite cutoff is real and nonnegative. -/
theorem critical_line_truncated_sum_real_nonnegative
    (Z : ZeroData) (g : WeilTestFunction) (T : ℝ) :
    (∑ n ∈ (Z.symmetricIndices T).filter
      (fun n => (Z.zero n).re = criticalAbscissa),
      zeroSummand Z (convolutionSquare g) n).im = 0 ∧
    0 ≤ (∑ n ∈ (Z.symmetricIndices T).filter
      (fun n => (Z.zero n).re = criticalAbscissa),
      zeroSummand Z (convolutionSquare g) n).re := by
  classical
  constructor
  · rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro n hn
    exact (critical_line_zero_summand_real_nonnegative Z g n
      (Finset.mem_filter.mp hn).2).1
  · rw [Complex.re_sum]
    exact Finset.sum_nonneg fun n hn =>
      (critical_line_zero_summand_real_nonnegative Z g n
        (Finset.mem_filter.mp hn).2).2

/-- Every finite zero cutoff is the sum of its critical-line and off-line filters. -/
theorem truncated_zero_sum_critical_offline_split
    (Z : ZeroData) (g : WeilTestFunction) (T : ℝ) :
    truncatedZeroSum Z (convolutionSquare g) T =
      (∑ n ∈ (Z.symmetricIndices T).filter
        (fun n => (Z.zero n).re = criticalAbscissa),
        zeroSummand Z (convolutionSquare g) n) +
      ∑ n ∈ (Z.symmetricIndices T).filter
        (fun n => (Z.zero n).re ≠ criticalAbscissa),
        zeroSummand Z (convolutionSquare g) n := by
  classical
  unfold truncatedZeroSum
  rw [Finset.sum_filter_add_sum_filter_not]

/-- The combined critical/off-line split has the explicit-formula limit. -/
theorem critical_offline_split_tendsto_explicit_formula
    (Z : ZeroData) (g : WeilTestFunction)
    (hZero : SymmetricConvergent Z (convolutionSquare g))
    (hArch : ArchimedeanConvergent (convolutionSquare g)) :
    Tendsto
      (fun T : ℝ =>
        (∑ n ∈ (Z.symmetricIndices T).filter
          (fun n => (Z.zero n).re = criticalAbscissa),
          zeroSummand Z (convolutionSquare g) n) +
        ∑ n ∈ (Z.symmetricIndices T).filter
          (fun n => (Z.zero n).re ≠ criticalAbscissa),
          zeroSummand Z (convolutionSquare g) n)
      atTop
      (nhds (poleTerm (convolutionSquare g) - primeTerm (convolutionSquare g) +
        archimedeanTerm (convolutionSquare g) hArch)) := by
  rw [← weil_explicit_formula Z (convolutionSquare g) hZero hArch]
  simpa only [truncated_zero_sum_critical_offline_split] using
    truncatedZeroSum_tendsto Z (convolutionSquare g) hZero

example (Z : ZeroData) (g : WeilTestFunction) (n : ℕ)
    (hline : (Z.zero n).re = criticalAbscissa) :
    0 ≤ (zeroSummand Z (convolutionSquare g) n).re :=
  (critical_line_zero_summand_real_nonnegative Z g n hline).2

end

end D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine
