/- GID: D5/S3/Quantum/Information/QubitNormalFormState
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/QubitNormalFormState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual closed-disk qubit density matrices and their natural-log spectral entropy. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.InputInformationBalance
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Information.QubitNormalFormState
open _root_.Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The determinant formula for the natural-log spectral entropy of any qubit density.
The eigenvalue argument is shared with FormationBounds' original bits-valued statement. -/
theorem qubit_spectral_entropy_det (τ : Matrix (Fin 2) (Fin 2) ℂ)
    (hτ : τ.PosSemidef) (ht : τ.trace = 1) :
    spectralEntropy hτ.1 = Real.binEntropy ((1 - Real.sqrt (1 - 4 * τ.det.re)) / 2) := by
  let a : ℝ := hτ.1.eigenvalues 0
  let b : ℝ := hτ.1.eigenvalues 1
  have ha : 0 ≤ a := hτ.eigenvalues_nonneg 0
  have hb : 0 ≤ b := hτ.eigenvalues_nonneg 1
  have hab : a+b=1 := by
    have hh := congrArg Complex.re hτ.1.trace_eq_sum_eigenvalues
    simpa [ht,Fin.sum_univ_two,a,b] using hh.symm
  have hdet : τ.det.re = a*b := by
    have hh := congrArg Complex.re hτ.1.det_eq_prod_eigenvalues
    simpa [Fin.prod_univ_two,a,b] using hh
  have hroot : Real.sqrt (1-4*τ.det.re) = |a-b| := by
    rw [hdet, show 1-4*(a*b)=(a-b)^2 by nlinarith [hab], Real.sqrt_sq_eq_abs]
  simp only [spectralEntropy, Fin.sum_univ_two]
  change Real.negMulLog a + Real.negMulLog b = _
  rw [hroot]
  rcases le_total a b with hab' | hba'
  · rw [abs_of_nonpos (by linarith : a-b ≤ 0)]
    have hr : (1- -(a-b))/2 = a := by linarith
    rw [hr]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,show 1-a=b by linarith]
  · rw [abs_of_nonneg (by linarith : 0 ≤ a-b)]
    have hr : (1-(a-b))/2 = b := by linarith
    rw [hr]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,show 1-b=a by linarith,add_comm]

/-- The matrix (I+xX+zZ)/2 in the computational basis. -/
def qubitMatrix (x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + (z : ℂ)) / 2, (x : ℂ) / 2; (x : ℂ) / 2, (1 - (z : ℂ)) / 2]

private lemma qubit_hermitian (x z : ℝ) : (qubitMatrix x z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitMatrix, Matrix.conjTranspose_apply]

private lemma qubit_trace (x z : ℝ) : (qubitMatrix x z).trace = 1 := by
  simp [qubitMatrix, Matrix.trace, Fin.sum_univ_two]
  ring

private lemma qubit_det (x z : ℝ) : (qubitMatrix x z).det.re = (1 - x ^ 2 - z ^ 2) / 4 := by
  simp [qubitMatrix, Matrix.det_fin_two, Complex.mul_re, Complex.div_re]
  ring

private lemma qubit_pos {x z : ℝ} (h : x ^ 2 + z ^ 2 ≤ 1) :
    (qubitMatrix x z).PosSemidef := by
  have hH := qubit_hermitian x z
  have ht := congrArg Complex.re hH.trace_eq_sum_eigenvalues
  rw [qubit_trace] at ht
  simp only [Fin.sum_univ_two, Complex.add_re, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.one_re] at ht
  have hd := congrArg Complex.re hH.det_eq_prod_eigenvalues
  rw [qubit_det] at hd
  simp only [Fin.prod_univ_two, Complex.mul_re, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hd
  have hp : 0 ≤ hH.eigenvalues 0 * hH.eigenvalues 1 := by nlinarith [h]
  have h0 : 0 ≤ hH.eigenvalues 0 := by nlinarith [sq_nonneg (hH.eigenvalues 0)]
  have h1 : 0 ≤ hH.eigenvalues 1 := by nlinarith [sq_nonneg (hH.eigenvalues 1)]
  apply hH.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  fin_cases i
  · exact h0
  · exact h1

/-- The full closed disk is allowed; no inverse or strictly positive eigenvalue is required. -/
def qubitState (x z : ℝ) (h : x ^ 2 + z ^ 2 ≤ 1) : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (qubitMatrix x z),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (qubit_pos h).nonneg, qubit_trace x z⟩

private lemma spectral_qubit_entropy (x z : ℝ) (h : x ^ 2 + z ^ 2 ≤ 1) :
    spectralEntropy (qubit_hermitian x z) =
      Real.binEntropy ((1 + Real.sqrt (x ^ 2 + z ^ 2)) / 2) := by
  have he' := qubit_spectral_entropy_det (qubitMatrix x z) (qubit_pos h) (qubit_trace x z)
  have hr : 1 - 4 * (qubitMatrix x z).det.re = x ^ 2 + z ^ 2 := by rw [qubit_det]; ring
  rw [hr] at he'
  rw [← Real.binEntropy_one_sub ((1 + Real.sqrt (x ^ 2 + z ^ 2)) / 2)]
  convert he' using 1
  congr 1
  ring

/-- The canonical CFC von Neumann entropy equals the actual qubit spectral formula, in nats. -/
theorem qubit_state_entropy (x z : ℝ) (h : x ^ 2 + z ^ 2 ≤ 1) :
    D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy (qubitState x z h) =
      Real.binEntropy ((1 + Real.sqrt (x ^ 2 + z ^ 2)) / 2) := by
  have hs :
      D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
          (qubitState x z h) =
        spectralEntropy (qubit_hermitian x z) := by
    convert D5.S3.Quantum.Information.InputInformationBalance.entropy_eq_sum
      (qubitState x z h) using 1 <;> simp only [spectralEntropy] <;> congr
  rw [hs]
  exact spectral_qubit_entropy x z h

/-- Symmetric binary Holevo entropy of the two actual density states, with no support division. -/
def qubitHolevo (x z : ℝ) (h : x ^ 2 + z ^ 2 ≤ 1) : ℝ :=
  D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
      (qubitState x 0 (by nlinarith [sq_nonneg z])) -
    (D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy (qubitState x z h) +
      D5.S3.Quantum.Divergence.VonNeumannEntropyPinching.vonNeumannEntropy
        (qubitState x (-z) (by nlinarith [h]))) / 2

#print axioms qubit_state_entropy
end D5.S3.Quantum.Information.QubitNormalFormState
