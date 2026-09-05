/- GID: D5/S3/Weil/ZetaBridge/FiniteMixedWeilMajorant
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/FiniteMixedWeilMajorant
   mirror-E: none(waiver:uniform-mixed-term-bound)
   anchors: []
   digest: Expand every finite Weil synthesis into all mixed convolution terms and derive one absolutely summable coefficient-uniform majorant. -/

import D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
import D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
import D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare

/-!
# Uniform control of all mixed Weil terms

The diagonal majorants of separate tests do not control a negative subspace.
This node uses actual mixed tests `g_i * involution g_j`. Their zero sums are
absolutely summable by the existing zeta explicit-formula owner. Expanding a
finite synthesis yields all coefficient cross terms. Their norms are bounded
by one finite coefficient energy times a fixed summable majorant, independent
of both the coefficient vector and the later convolution-power depth.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Fourier.ConvolutionPowerAmplification
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- An actual mixed convolution summand, with analytic multiplicity included. -/
def mixedWeilSummand (Z : ZeroData) (g h : WeilTestFunction) (n : ℕ) : ℂ :=
  zeroSummand Z (convolve g (involution h)) n

/-- Exact polarized complex-frequency factorization. -/
theorem mixedWeilSummand_factorization
    (Z : ZeroData) (g h : WeilTestFunction) (n : ℕ) :
    mixedWeilSummand Z g h n =
      (Z.multiplicity n : ℂ) * fourierLaplace g (Z.gamma n) *
        conj (fourierLaplace h (conj (Z.gamma n))) := by
  rw [mixedWeilSummand, zeroSummand, fourierLaplace_convolve_complex,
    fourierLaplace_involution_conj]
  ring

/-- Mixed summability is a specialization of the existing theorem for actual
compact smooth Weil tests; no new analytic hypothesis is required. -/
theorem mixedWeilSummand_summable
    (Z : ZeroData) (g h : WeilTestFunction) :
    Summable (mixedWeilSummand Z g h) :=
  zeroSummand_summable_of_zeroData Z (convolve g (involution h))

/-- Full expansion of a synthesized convolution square, including every
mixed term. -/
theorem zeroSummand_finite_synthesis_expansion
    (Z : ZeroData) (a : ι → ℂ) (g : ι → WeilTestFunction) (n : ℕ) :
    zeroSummand Z (convolutionSquare (finiteWeilLinearCombination a g)) n =
      ∑ i, ∑ j, (a i * conj (a j)) * mixedWeilSummand Z (g i) (g j) n := by
  rw [zeroSummand, fourierLaplace_convolutionSquare_complex,
    fourierLaplace_finiteWeilLinearCombination,
    fourierLaplace_finiteWeilLinearCombination]
  simp_rw [mixedWeilSummand_factorization, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every coefficient cross product is bounded by the complete coefficient
energy, including when the finite index type is empty. -/
theorem coefficient_cross_norm_le_energy (a : ι → ℂ) (i j : ι) :
    ‖a i * conj (a j)‖ ≤ finiteComplexEnergy a := by
  rw [norm_mul, Complex.norm_conj]
  have hi : ‖a i‖ ^ 2 ≤ finiteComplexEnergy a := by
    simpa only [finiteComplexEnergy, Complex.normSq_eq_norm_sq] using
      (Finset.single_le_sum
        (fun k _ => Complex.normSq_nonneg (a k)) (Finset.mem_univ i))
  have hj : ‖a j‖ ^ 2 ≤ finiteComplexEnergy a := by
    simpa only [finiteComplexEnergy, Complex.normSq_eq_norm_sq] using
      (Finset.single_le_sum
        (fun k _ => Complex.normSq_nonneg (a k)) (Finset.mem_univ j))
  nlinarith [sq_nonneg (‖a i‖ - ‖a j‖)]

/-- The fixed mixed-term majorant for a finite test basis. -/
def finiteMixedMajorant (Z : ZeroData) (g : ι → WeilTestFunction)
    (n : ℕ) : ℝ :=
  ∑ i, ∑ j, ‖mixedWeilSummand Z (g i) (g j) n‖

theorem finiteMixedMajorant_nonneg
    (Z : ZeroData) (g : ι → WeilTestFunction) (n : ℕ) :
    0 ≤ finiteMixedMajorant Z g n := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => norm_nonneg _

/-- The finite sum of all mixed absolute summands is summable. -/
theorem finiteMixedMajorant_summable
    (Z : ZeroData) (g : ι → WeilTestFunction) :
    Summable (finiteMixedMajorant Z g) := by
  unfold finiteMixedMajorant
  apply summable_sum
  intro i _
  apply summable_sum
  intro j _
  exact (mixedWeilSummand_summable Z (g i) (g j)).norm

/-- One uniform pointwise bound controls every synthesized square, not merely
its individual basis vectors. -/
theorem zeroSummand_finite_synthesis_norm_le
    (Z : ZeroData) (a : ι → ℂ) (g : ι → WeilTestFunction) (n : ℕ) :
    ‖zeroSummand Z (convolutionSquare (finiteWeilLinearCombination a g)) n‖ ≤
      finiteComplexEnergy a * finiteMixedMajorant Z g n := by
  rw [zeroSummand_finite_synthesis_expansion]
  calc
    ‖∑ i, ∑ j, (a i * conj (a j)) * mixedWeilSummand Z (g i) (g j) n‖ ≤
        ∑ i, ‖∑ j, (a i * conj (a j)) * mixedWeilSummand Z (g i) (g j) n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ∑ j,
        ‖(a i * conj (a j)) * mixedWeilSummand Z (g i) (g j) n‖ := by
      exact Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j,
        finiteComplexEnergy a * ‖mixedWeilSummand Z (g i) (g j) n‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (coefficient_cross_norm_le_energy a i j)
        (norm_nonneg _)
    _ = finiteComplexEnergy a * finiteMixedMajorant Z g n := by
      simp only [finiteMixedMajorant, Finset.mul_sum]

/-- The finite real constant used in the uniform Burnol estimate. It is
independent of the coefficient vector and convolution-power depth. -/
def finiteMixedMajorantTotal (Z : ZeroData) (g : ι → WeilTestFunction) : ℝ :=
  ∑' n : ℕ, finiteMixedMajorant Z g n

theorem finiteMixedMajorantTotal_nonneg
    (Z : ZeroData) (g : ι → WeilTestFunction) :
    0 ≤ finiteMixedMajorantTotal Z g :=
  tsum_nonneg (finiteMixedMajorant_nonneg Z g)

/-- Uniform absolute-sum estimate for the entire finite test family. -/
theorem finite_synthesis_absolute_sum_le
    (Z : ZeroData) (a : ι → ℂ) (g : ι → WeilTestFunction) :
    (∑' n : ℕ,
      ‖zeroSummand Z (convolutionSquare (finiteWeilLinearCombination a g)) n‖) ≤
        finiteComplexEnergy a * finiteMixedMajorantTotal Z g := by
  have hleft :=
    (zeroSummand_summable_of_zeroData Z
      (convolutionSquare (finiteWeilLinearCombination a g))).norm
  have hright := (finiteMixedMajorant_summable Z g).mul_left (finiteComplexEnergy a)
  calc
    _ ≤ ∑' n : ℕ, finiteComplexEnergy a * finiteMixedMajorant Z g n :=
      hleft.tsum_le_tsum (zeroSummand_finite_synthesis_norm_le Z a g) hright
    _ = _ := by rw [tsum_mul_left]; rfl

#print axioms mixedWeilSummand_summable
#print axioms zeroSummand_finite_synthesis_expansion
#print axioms finiteMixedMajorant_summable
#print axioms finite_synthesis_absolute_sum_le

end D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
