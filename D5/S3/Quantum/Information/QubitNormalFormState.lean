/- GID: D5/S3/Quantum/Information/QubitNormalFormState
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/QubitNormalFormState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual closed-disk qubit density matrices and their natural-log spectral entropy. -/

import D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Information.QubitNormalFormState
open Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

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
  simp only [Fin.sum_univ_two, Complex.add_re, Complex.ofReal_re, Complex.one_re] at ht
  have hd := congrArg Complex.re hH.det_eq_prod_eigenvalues
  rw [qubit_det] at hd
  simp only [Fin.prod_univ_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
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
  have he := D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.qubit_entropy_det
    (qubitMatrix x z) (qubit_pos h) (qubit_trace x z)
  rw [D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.S,
    dif_pos (qubit_hermitian x z)] at he
  have hf (p : ℝ) : D5.S3.Quantum.CloningMachine.binaryEntropyBits p =
      Real.binEntropy p / Real.log 2 := by
    simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb,
      Real.binEntropy, Real.log_inv]
    ring
  rw [hf] at he
  have he' := (div_left_inj' (show Real.log 2 ≠ 0 by positivity)).mp he
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
  rw [entropy_eq_spectral]
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
