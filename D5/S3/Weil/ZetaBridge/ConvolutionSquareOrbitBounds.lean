/- GID: D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds
   mirror-E: none(waiver:structural-closure-properties-only)
   anchors: []
   digest: Complex-frequency factorization and off-line orbit energy bounds. -/

import D5.S3.Weil.ZetaBridge.ConvolutionSquareOffLineOrbits
import Mathlib.Analysis.Convolution

namespace D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds

open MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOffLineOrbits
open scoped ComplexConjugate Convolution

noncomputable section

private theorem fourierKernel_add (z : ℂ) (x y : ℝ) :
    fourierKernel z (x + y) = fourierKernel z x * fourierKernel z y := by
  simp only [fourierKernel]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem twisted_integrable (g : WeilTestFunction) (z : ℂ) :
    Integrable (fun x : ℝ => fourierKernel z x * g x) := by
  have hk : Continuous (fun x : ℝ => fourierKernel z x) := by
    unfold fourierKernel
    fun_prop
  apply (hk.mul g.continuous).integrable_of_hasCompactSupport
  exact g.hasCompactSupport.mul_left

private theorem twisted_involution_integrable (g : WeilTestFunction) (z : ℂ) :
    Integrable (fun x : ℝ => fourierKernel z x * involution g x) := by
  have hk : Continuous (fun x : ℝ => fourierKernel z x) := by
    unfold fourierKernel
    fun_prop
  apply (hk.mul (involution g).continuous).integrable_of_hasCompactSupport
  exact (involution g).hasCompactSupport.mul_left

/-- The complex Fourier-Laplace transform factors across a convolution square. -/
theorem fourierLaplace_convolutionSquare_complex (g : WeilTestFunction) (z : ℂ) :
    fourierLaplace (convolutionSquare g) z =
      fourierLaplace g z * conj (fourierLaplace g (conj z)) := by
  let f : ℝ → ℂ := fun x => fourierKernel z x * g x
  let h : ℝ → ℂ := fun x => fourierKernel z x * involution g x
  have hf : Integrable f := by
    simpa [f] using twisted_integrable g z
  have hh : Integrable h := by
    simpa [h] using twisted_involution_integrable g z
  have hconv (x : ℝ) :
      (f ⋆[complexMul, volume] h) x = fourierKernel z x * convolutionSquare g x := by
    rw [convolution_def]
    change (∫ t : ℝ,
      (fourierKernel z t * g t) *
        (fourierKernel z (x - t) * involution g (x - t))) =
      fourierKernel z x * (∫ t : ℝ, g t * involution g (x - t))
    rw [← integral_const_mul (fourierKernel z x)]
    apply integral_congr_ae
    filter_upwards with t
    calc
      fourierKernel z t * g t *
          (fourierKernel z (x - t) * involution g (x - t)) =
          (fourierKernel z t * fourierKernel z (x - t)) *
            (g t * involution g (x - t)) := by ring
      _ = fourierKernel z x * (g t * involution g (x - t)) := by
        rw [← fourierKernel_add z t (x - t)]
        congr 2
        ring
  calc
    fourierLaplace (convolutionSquare g) z =
        ∫ x : ℝ, fourierKernel z x * convolutionSquare g x := rfl
    _ = ∫ x : ℝ, (f ⋆[complexMul, volume] h) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact (hconv x).symm
    _ = complexMul (∫ x : ℝ, f x) (∫ x : ℝ, h x) :=
      integral_convolution (L := complexMul) (ν := volume) (μ := volume) hf hh
    _ = (∫ x : ℝ, fourierKernel z x * g x) *
        (∫ x : ℝ, fourierKernel z x * involution g x) := by
      rfl
    _ = fourierLaplace g z * fourierLaplace (involution g) z := by
      rfl
    _ = fourierLaplace g z * conj (fourierLaplace g (conj z)) := by
      rw [fourierLaplace_involution_conj]

/-- Every off-line four-point orbit has an energy-controlled real value. -/
theorem off_line_zero_orbit_sum_energy_bounds
    (Z : ZeroData) (g : WeilTestFunction) (n : ℕ)
    (hC : Z.conjugation n ≠ n)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    -(2 * (Z.multiplicity n : ℝ) *
      (Complex.normSq (fourierLaplace g (Z.gamma n)) +
        Complex.normSq (fourierLaplace g (conj (Z.gamma n))))) ≤
      (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ),
        zeroSummand Z (convolutionSquare g) k).re ∧
      (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ),
        zeroSummand Z (convolutionSquare g) k).re ≤
      2 * (Z.multiplicity n : ℝ) *
        (Complex.normSq (fourierLaplace g (Z.gamma n)) +
          Complex.normSq (fourierLaplace g (conj (Z.gamma n)))) := by
  let A : ℂ := fourierLaplace g (Z.gamma n)
  let B : ℂ := fourierLaplace g (conj (Z.gamma n))
  have hLower :
      -(Complex.normSq A + Complex.normSq B) ≤ 2 * (A * conj B).re := by
    have h := Complex.normSq_nonneg (A + B)
    rw [Complex.normSq_add] at h
    linarith
  have hUpper :
      2 * (A * conj B).re ≤ Complex.normSq A + Complex.normSq B := by
    have h := Complex.normSq_nonneg (A - B)
    rw [Complex.normSq_sub] at h
    linarith
  have hOrbit := off_line_zero_orbit_sum_eq_four_mul_re Z g n hC hOff
  constructor
  · rw [hOrbit]
    simp only [Complex.ofReal_re]
    rw [zeroSummand, fourierLaplace_convolutionSquare_complex]
    change -(2 * (Z.multiplicity n : ℝ) *
      (Complex.normSq (fourierLaplace g (Z.gamma n)) +
          Complex.normSq (fourierLaplace g (conj (Z.gamma n))))) ≤
      4 * ((Z.multiplicity n : ℂ) *
        (fourierLaplace g (Z.gamma n) *
          conj (fourierLaplace g (conj (Z.gamma n))))).re
    have h := hLower
    dsimp [A, B] at h ⊢
    rw [Complex.mul_re]
    norm_num at *
    nlinarith [Z.multiplicity_pos n]
  · rw [hOrbit]
    simp only [Complex.ofReal_re]
    rw [zeroSummand, fourierLaplace_convolutionSquare_complex]
    change 4 * ((Z.multiplicity n : ℂ) *
        (fourierLaplace g (Z.gamma n) *
          conj (fourierLaplace g (conj (Z.gamma n))))).re ≤
      2 * (Z.multiplicity n : ℝ) *
        (Complex.normSq (fourierLaplace g (Z.gamma n)) +
        Complex.normSq (fourierLaplace g (conj (Z.gamma n))))
    have h := hUpper
    dsimp [A, B] at h ⊢
    rw [Complex.mul_re]
    norm_num at *
    nlinarith [Z.multiplicity_pos n]

example (Z : ZeroData) (g : WeilTestFunction) (n : ℕ)
    (hC : Z.conjugation n ≠ n)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    0 ≤ 2 * (Z.multiplicity n : ℝ) *
      (Complex.normSq (fourierLaplace g (Z.gamma n)) +
        Complex.normSq (fourierLaplace g (conj (Z.gamma n)))) := by
  have hm : 0 ≤ (Z.multiplicity n : ℝ) := Nat.cast_nonneg _
  have hA := Complex.normSq_nonneg (fourierLaplace g (Z.gamma n))
  have hB := Complex.normSq_nonneg (fourierLaplace g (conj (Z.gamma n)))
  exact mul_nonneg (mul_nonneg (by norm_num) hm) (add_nonneg hA hB)

end

end D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
