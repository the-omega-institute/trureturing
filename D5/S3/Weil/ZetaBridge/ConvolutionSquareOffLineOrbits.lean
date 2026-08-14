/- GID: D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits
   mirror-E: none(waiver:structural-closure-properties-only)
   anchors: []
   digest: Organize off-line convolution-square zero summands into real symmetry orbits. -/

import D5.S3.Weil.ZetaBridge.ConvolutionSquareCriticalLine
import D5.S3.Zeros.Symmetry.ZeroOrbitCardinality

namespace D5.S3.Weil.ZetaBridge.ConvolutionSquareOffLineOrbits

open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZeroSum
open D5.S3.Zeros.Symmetry.ZeroOrbitCardinality
open scoped ComplexConjugate

noncomputable section

private theorem convolutionSquare_involution (g : WeilTestFunction) :
    involution (convolutionSquare g) = convolutionSquare g := by
  ext x
  have hswap :
      convolutionSquare g x = ∫ t : ℝ, g (x - t) * conj (g t) := by
    rw [convolutionSquare]
    change
      MeasureTheory.convolution g (involution g) complexMul MeasureTheory.volume x = _
    rw [MeasureTheory.convolution_eq_swap]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    simp only [involution_apply]
    rw [g.even t]
    rfl
  rw [involution_apply, convolutionSquare_even, convolutionSquare_apply, ← integral_conj]
  rw [← convolutionSquare_apply, hswap]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [map_mul, Complex.conj_conj]
  have ht := g.even (t - x)
  simp only [neg_sub] at ht
  rw [ht]
  ring

/-- Conjugate zero indices contribute conjugate convolution-square summands. -/
theorem convolution_square_zero_summand_conjugation
    (Z : ZeroData) (g : WeilTestFunction) (n : ℕ) :
    zeroSummand Z (convolutionSquare g) (Z.conjugation n) =
      conj (zeroSummand Z (convolutionSquare g) n) := by
  simp only [zeroSummand, Z.multiplicity_conjugation, Z.gamma_conjugation]
  rw [fourierLaplace_neg]
  have htransform :=
    fourierLaplace_involution_conj (convolutionSquare g) (conj (Z.gamma n))
  rw [convolutionSquare_involution] at htransform
  rw [htransform]
  simp only [Complex.conj_conj, map_mul, map_natCast]

/-- A four-point off-line orbit sums to four times the real part of one summand. -/
theorem off_line_zero_orbit_sum_eq_four_mul_re
    (Z : ZeroData) (g : WeilTestFunction) (n : ℕ)
    (hC : Z.conjugation n ≠ n)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ),
        zeroSummand Z (convolutionSquare g) k) =
      ((4 * (zeroSummand Z (convolutionSquare g) n).re : ℝ) : ℂ) := by
  classical
  have hcard := zero_orbit_card_four_of_off_line Z n hC hOff
  have hnMem :
      n ∉ ({Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ) := by
    intro hn
    have heq :
        ({n, Z.reflection n, Z.conjugation n,
          Z.conjugation (Z.reflection n)} : Finset ℕ) =
          {Z.reflection n, Z.conjugation n,
            Z.conjugation (Z.reflection n)} :=
      Finset.insert_eq_of_mem hn
    rw [heq] at hcard
    have hle :
        ({Z.reflection n, Z.conjugation n,
          Z.conjugation (Z.reflection n)} : Finset ℕ).card ≤ 3 :=
      Finset.card_le_three
    omega
  rw [Finset.card_insert_of_notMem hnMem] at hcard
  have hRMem :
      Z.reflection n ∉
        ({Z.conjugation n, Z.conjugation (Z.reflection n)} : Finset ℕ) := by
    intro hR
    have heq :
        ({Z.reflection n, Z.conjugation n,
          Z.conjugation (Z.reflection n)} : Finset ℕ) =
          {Z.conjugation n, Z.conjugation (Z.reflection n)} :=
      Finset.insert_eq_of_mem hR
    rw [heq] at hcard
    have hle :
        ({Z.conjugation n,
          Z.conjugation (Z.reflection n)} : Finset ℕ).card ≤ 2 :=
      Finset.card_le_two
    omega
  rw [Finset.card_insert_of_notMem hRMem] at hcard
  have hCMem :
      Z.conjugation n ∉ ({Z.conjugation (Z.reflection n)} : Finset ℕ) := by
    intro hC'
    have heq :
        ({Z.conjugation n,
          Z.conjugation (Z.reflection n)} : Finset ℕ) =
          {Z.conjugation (Z.reflection n)} :=
      Finset.insert_eq_of_mem hC'
    rw [heq] at hcard
    simp at hcard
  rw [Finset.sum_insert hnMem, Finset.sum_insert hRMem,
    Finset.sum_insert hCMem, Finset.sum_singleton]
  rw [zeroSummand_reflection,
    convolution_square_zero_summand_conjugation,
    convolution_square_zero_summand_conjugation,
    zeroSummand_reflection]
  apply Complex.ext
  · simp
    ring
  · simp

/-- The off-line part of every finite symmetric cutoff is real. -/
theorem off_line_truncated_sum_real
    (Z : ZeroData) (g : WeilTestFunction) (T : ℝ) :
    (∑ n ∈ (Z.symmetricIndices T).filter
      (fun n => (Z.zero n).re ≠ criticalAbscissa),
      zeroSummand Z (convolutionSquare g) n).im = 0 := by
  classical
  let s := (Z.symmetricIndices T).filter
    (fun n => (Z.zero n).re ≠ criticalAbscissa)
  let f := fun n => zeroSummand Z (convolutionSquare g) n
  have hstable (n : ℕ) : n ∈ s ↔ Z.conjugation n ∈ s := by
    simp [s, Z.zero_conjugation]
  have hsum : (∑ n ∈ s, f (Z.conjugation n)) = ∑ n ∈ s, f n := by
    exact Finset.sum_equiv Z.conjugation hstable (fun _ _ => rfl)
  have hreal : conj (∑ n ∈ s, f n) = ∑ n ∈ s, f n := by
    calc
      conj (∑ n ∈ s, f n) = ∑ n ∈ s, conj (f n) := by rw [map_sum]
      _ = ∑ n ∈ s, f (Z.conjugation n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (convolution_square_zero_summand_conjugation Z g n).symm
      _ = ∑ n ∈ s, f n := hsum
  have him := congrArg Complex.im hreal
  rw [Complex.conj_im] at him
  change (∑ n ∈ s, f n).im = 0
  linarith

example (Z : ZeroData) (g : WeilTestFunction) (T : ℝ) :
    (∑ n ∈ (Z.symmetricIndices T).filter
      (fun n => (Z.zero n).re ≠ criticalAbscissa),
      zeroSummand Z (convolutionSquare g) n).im = 0 :=
  off_line_truncated_sum_real Z g T

end

end D5.S3.Weil.ZetaBridge.ConvolutionSquareOffLineOrbits
