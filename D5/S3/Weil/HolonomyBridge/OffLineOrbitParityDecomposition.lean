/- GID: D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition
   generality: I
   mirror-B: D5/B/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Off-line zero orbits split into even energy minus odd energy. -/

import D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
import Mathlib.Tactic

/-!
# Off-line orbit parity decomposition

For one off-line zero orbit, evaluate the test seed at the complex spectral
parameter and at its conjugate.  Their half-sum is the even channel and their
half-difference is the odd channel.  Complex-frequency factorization of the
convolution square then turns the real orbit contribution into

`even energy - odd energy`.

Both channel energies are nonnegative.  Adding the odd energy therefore
completes the orbit contribution to the even energy.  The theorem neither
asserts that an off-line orbit exists nor supplies a prime-side construction
of the odd correction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition

open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOffLineOrbits
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open scoped ComplexConjugate

/-- The symmetric spectral channel of a complex-frequency pair. -/
def evenSpectralChannel (first second : ℂ) : ℂ :=
  (first + second) / 2

/-- The antisymmetric spectral channel of a complex-frequency pair. -/
def oddSpectralChannel (first second : ℂ) : ℂ :=
  (first - second) / 2

/-- The multiplicity-weighted nonnegative even channel energy. -/
def orbitEvenEnergy (multiplicity : ℕ) (first second : ℂ) : ℝ :=
  4 * (multiplicity : ℝ) *
    Complex.normSq (evenSpectralChannel first second)

/-- The multiplicity-weighted nonnegative odd channel correction. -/
def orbitOddEnergy (multiplicity : ℕ) (first second : ℂ) : ℝ :=
  4 * (multiplicity : ℝ) *
    Complex.normSq (oddSpectralChannel first second)

private theorem channel_energy_difference (first second : ℂ) :
    Complex.normSq (evenSpectralChannel first second) -
        Complex.normSq (oddSpectralChannel first second) =
      (first * conj second).re := by
  unfold evenSpectralChannel oddSpectralChannel
  rw [Complex.normSq_div, Complex.normSq_div,
    Complex.normSq_add, Complex.normSq_sub]
  norm_num
  ring

/--
A four-point off-line zero orbit has a canonical parity split.  Its real
convolution-square contribution is the even energy minus the odd energy.  The
odd term is a positive correction, and adding it leaves the nonnegative even
energy.
-/
theorem off_line_orbit_parity_decomposition
    (Z : ZeroData) (g : WeilTestFunction) (n : ℕ)
    (hConjugate : Z.conjugation n ≠ n)
    (hOffLine : (Z.zero n).re ≠ criticalAbscissa) :
    let first := fourierLaplace g (Z.gamma n)
    let second := fourierLaplace g (conj (Z.gamma n))
    let orbitValue :=
      (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ),
        zeroSummand Z (convolutionSquare g) k).re
    orbitValue =
        orbitEvenEnergy (Z.multiplicity n) first second -
          orbitOddEnergy (Z.multiplicity n) first second ∧
      0 ≤ orbitOddEnergy (Z.multiplicity n) first second ∧
      orbitValue + orbitOddEnergy (Z.multiplicity n) first second =
        orbitEvenEnergy (Z.multiplicity n) first second ∧
      0 ≤ orbitEvenEnergy (Z.multiplicity n) first second := by
  dsimp only
  let first : ℂ := fourierLaplace g (Z.gamma n)
  let second : ℂ := fourierLaplace g (conj (Z.gamma n))
  have hOrbit :=
    off_line_zero_orbit_sum_eq_four_mul_re Z g n hConjugate hOffLine
  have hRaw :
      (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ),
        zeroSummand Z (convolutionSquare g) k).re =
      4 * (Z.multiplicity n : ℝ) *
        (Complex.normSq (evenSpectralChannel first second) -
          Complex.normSq (oddSpectralChannel first second)) := by
    rw [hOrbit]
    simp only [Complex.ofReal_re]
    rw [zeroSummand, fourierLaplace_convolutionSquare_complex]
    change 4 * (((Z.multiplicity n : ℂ) *
        (first * conj second)).re) =
      4 * (Z.multiplicity n : ℝ) *
        (Complex.normSq (evenSpectralChannel first second) -
          Complex.normSq (oddSpectralChannel first second))
    rw [Complex.mul_re]
    norm_num
    rw [channel_energy_difference]
    simp only [map_re, map_im]
    ring
  have hDecomposition :
      (∑ k ∈ ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ),
        zeroSummand Z (convolutionSquare g) k).re =
      orbitEvenEnergy (Z.multiplicity n) first second -
        orbitOddEnergy (Z.multiplicity n) first second := by
    rw [hRaw]
    unfold orbitEvenEnergy orbitOddEnergy
    ring
  have hEvenNonnegative :
      0 ≤ orbitEvenEnergy (Z.multiplicity n) first second := by
    unfold orbitEvenEnergy
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Complex.normSq_nonneg _)
  have hOddNonnegative :
      0 ≤ orbitOddEnergy (Z.multiplicity n) first second := by
    unfold orbitOddEnergy
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (Complex.normSq_nonneg _)
  refine ⟨hDecomposition, hOddNonnegative, ?_, hEvenNonnegative⟩
  rw [hDecomposition]
  ring

#print axioms off_line_orbit_parity_decomposition

end D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
