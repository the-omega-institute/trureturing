/- GID: D5/S3/Quantum/PureState/PhaseMemoryQubitAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseMemoryQubitAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit qubit encoders attain the clipped score for Walsh and symmetric Fourier phases. -/

import D5.S3.Quantum.PureState.PhaseMemoryCompact
import D5.S3.Quantum.PureState.PhaseMemorySaturatedFrame
import Mathlib.Tactic.Module

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open JointRecordDecoding (phaseVector)
open PhaseMemorySaturatedFrame (fourierTail fourier4)

namespace PhaseMemoryOptimized

noncomputable section

private abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

/-- Walsh characters in the Pauli order, with (s_3=s_1s_2). -/
def walsh4 : Fin 4 → Fin 4 → ℂ :=
  ![![1, 1, 1, 1], ![1, 1, -1, -1], ![1, -1, 1, -1], ![1, -1, -1, 1]]

theorem walsh4_norm (j i : Fin 4) : ‖walsh4 j i‖ = 1 := by
  fin_cases j <;> fin_cases i <;> norm_num [walsh4]

private def spin (a : ℝ) (z : ℂ) : Qubit :=
  !![(a : ℂ), z; star z, -(a : ℂ)]

private theorem spin_hermitian (a : ℝ) (z : ℂ) : (spin a z).conjTranspose = spin a z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spin]

private theorem trace_spin (a : ℝ) (z : ℂ) : trace (spin a z) = 0 := by
  simp [trace, diag, spin, Fin.sum_univ_two]

private theorem spin_sq (a : ℝ) (z : ℂ) :
    spin a z * spin a z = ((a : ℂ) ^ 2 + (Complex.normSq z : ℂ)) • (1 : Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spin, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.normSq_eq_conj_mul_self, pow_two] <;> ring

private def halfRoot : ℝ := (Real.sqrt 2)⁻¹

private theorem halfRoot_sq : halfRoot ^ 2 = (1 / 2 : ℝ) := by
  rw [halfRoot, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private def qubitKraus (basis : Fin 4 → Qubit) (e : Fin 2) : Matrix (Fin 2) (Fin 4) ℂ :=
  fun o i => (halfRoot : ℂ) * basis i o e

private def coefficient (basis : Fin 4 → Qubit) (v : Fin 4 → ℂ) : Qubit :=
  ∑ i, v i • basis i

private theorem qubitKraus_action (basis : Fin 4 → Qubit) (v : Fin 4 → ℂ) :
    (∑ e, qubitKraus basis e * rankOneDensity v * (qubitKraus basis e).conjTranspose) =
      ((halfRoot : ℂ) • coefficient basis v) * ((halfRoot : ℂ) • coefficient basis v).conjTranspose := by
  have hv (e : Fin 2) (o : Fin 2) :
      (qubitKraus basis e *ᵥ v) o = ((halfRoot : ℂ) • coefficient basis v) o e := by
    simp only [Matrix.mulVec, dotProduct, qubitKraus, coefficient, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hstar (e : Fin 2) (o : Fin 2) :
      (star v ᵥ* (qubitKraus basis e).conjTranspose) o =
        star ((qubitKraus basis e *ᵥ v) o) := by
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.conjTranspose_apply,
      star_sum, star_mul, mul_comm]
  ext o p
  simp only [rankOneDensity, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.sum_apply, Matrix.vecMulVec_apply, hstar, hv, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

private theorem qubit_attainment_of_coefficients
    (u : Fin 4 → Fin 4 → ℂ) (t : Fin 4 → ℝ) (r : ℝ) (hr : 0 < r)
    (basis : Fin 4 → Qubit)
    (hbasis : ∑ e, (qubitKraus basis e).conjTranspose * qubitKraus basis e = 1)
    (B : Fin 4 → Qubit)
    (hcoeff : ∀ j, coefficient basis (phaseVector u t j) = (t 0 : ℂ) • 1 + B j)
    (hHerm : ∀ j, (B j).conjTranspose = B j)
    (htrace : ∀ j, trace (B j) = 0)
    (hsq : ∀ j, B j * B j = (r : ℂ) ^ 2 • 1)
    (hsum : ∑ j, B j = 0) :
    (t 0 + r) ^ 2 / 4 ∈ successSet (Fin 2) (phaseVector u t) := by
  obtain ⟨Φ, hΦ⟩ := finite_kraus_quantum_channel _ hbasis
  let ρ : ℂ := r
  have hρ : ρ ≠ 0 := by simp [ρ, hr.ne']
  have hρstar : star ρ = ρ := Complex.conj_ofReal r
  let H (j : Fin 4) := ρ⁻¹ • B j
  have hH (j : Fin 4) : B j = ρ • H j := by
    dsimp only [H]
    rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
  have hHH (j : Fin 4) : H j * H j = 1 := by
    dsimp only [H]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hsq, smul_smul]
    change (ρ⁻¹ * ρ⁻¹ * ρ ^ 2) • (1 : Qubit) = 1
    rw [show ρ⁻¹ * ρ⁻¹ * ρ ^ 2 = 1 by field_simp, one_smul]
  let R (j : Fin 4) := (1 / 2 : ℂ) • (1 + H j)
  have hRH (j : Fin 4) : (R j).conjTranspose = R j := by
    simp [R, H, Matrix.conjTranspose_smul, hρstar, hHerm]
  have hRHmul (j : Fin 4) : R j * H j = R j := by
    simp [R, add_mul, hHH, add_comm]
  have hRR (j : Fin 4) : R j * R j = R j := by
    calc
      _ = (1 / 2 : ℂ) • (R j + R j * H j) := by
        change R j * ((1 / 2 : ℂ) • (1 + H j)) = _
        rw [mul_smul_comm, mul_add, mul_one]
      _ = R j := by rw [hRHmul]; module
  have hRtrace (j : Fin 4) : trace (R j) = 1 := by
    simp [R, H, Matrix.trace_smul, Matrix.trace_add, htrace, Matrix.trace_one]
  let D (j : Fin 4) := (1 / 2 : ℂ) • R j
  have hD : IsPOVM D := by
    constructor
    · intro j
      have hp : (R j).PosSemidef := by
        have h := Matrix.posSemidef_conjTranspose_mul_self (R j)
        rwa [hRH, hRR] at h
      exact hp.smul (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])
    · have hsumH : ∑ j, H j = 0 := by
        dsimp only [H]
        rw [← Finset.smul_sum, hsum, smul_zero]
      simp only [D, R, ← Finset.smul_sum, Finset.sum_add_distrib, hsumH, add_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      module
  refine ⟨Φ, D, hD, ?_⟩
  have hscore (j : Fin 4) :
      (trace (D j * CStarMatrix.ofMatrix.symm
        (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix (rankOneDensity (phaseVector u t j)))))).re =
        (t 0 + r) ^ 2 / 4 := by
    rw [hΦ, qubitKraus_action, hcoeff]
    let K : Qubit := (halfRoot : ℂ) • ((t 0 : ℂ) • 1 + B j)
    change (trace (D j * (K * K.conjTranspose))).re = _
    have hKH : K.conjTranspose = K := by
      simp [K, Matrix.conjTranspose_smul, hHerm]
    let eigenvalue : ℂ := ↑(halfRoot * (t 0 + r))
    have heig : R j * K = eigenvalue • R j := by
      simp only [K, mul_smul_comm, mul_add, mul_one, hH j, hRHmul, eigenvalue,
        Complex.ofReal_mul, Complex.ofReal_add, ρ]
      module
    rw [hKH, show D j = (1 / 2 : ℂ) • R j from rfl, smul_mul_assoc, ← mul_assoc,
      heig, smul_mul_assoc, heig,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, hRtrace]
    have heigenvalue : eigenvalue * (eigenvalue * 1) = (((t 0 + r) ^ 2 / 2 : ℝ) : ℂ) := by
      rw [mul_one, ← pow_two]
      dsimp only [eigenvalue]
      rw [← Complex.ofReal_pow]
      congr 1
      rw [mul_pow, halfRoot_sq]
      ring
    change ((1 / 2 : ℂ) * (eigenvalue * (eigenvalue * 1))).re = _
    rw [heigenvalue, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  simp only [score, hscore, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private def pauli : Fin 4 → Qubit :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

private theorem pauli_kraus_normalized :
    ∑ e, (qubitKraus pauli e).conjTranspose * qubitKraus pauli e = 1 := by
  have hq : (halfRoot : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, halfRoot_sq]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitKraus, pauli, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Complex.star_def, Complex.conj_I, Complex.I_sq, mul_assoc] <;>
    ring_nf <;> norm_num [hq, Complex.I_sq]

private def walshTail (t : Fin 4 → ℝ) (j : Fin 4) : Qubit :=
  spin (t 3 * (walsh4 j 3).re)
    ((t 1 : ℂ) * walsh4 j 1 - (t 2 : ℂ) * walsh4 j 2 * Complex.I)

/-- A fixed Pauli encoder and its four-outcome decoder attain the dominant Walsh score. -/
theorem walsh4_attains (t : Fin 4 → ℝ) (hr : 0 < fourierTail t) :
    (t 0 + fourierTail t) ^ 2 / 4 ∈ successSet (Fin 2) (phaseVector walsh4 t) := by
  apply qubit_attainment_of_coefficients walsh4 t (fourierTail t) hr pauli pauli_kraus_normalized
    (walshTail t)
  · intro j
    ext o e
    fin_cases j <;> fin_cases o <;> fin_cases e <;>
      norm_num [coefficient, phaseVector, pauli, walsh4, walshTail, spin, Fin.sum_univ_succ,
        Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, Complex.star_def, Complex.conj_I,
        Matrix.one_apply] <;> ring
  · intro j
    exact spin_hermitian _ _
  · intro j
    exact trace_spin _ _
  · intro j
    rw [walshTail, spin_sq]
    have hr2 : (fourierTail t) ^ 2 = t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 :=
      Real.sq_sqrt (by positivity)
    congr 1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_add, ← Complex.ofReal_pow, hr2]
    congr 1
    fin_cases j <;>
      norm_num [walsh4, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im] <;> ring
  · ext o e
    fin_cases o <;> fin_cases e <;>
      norm_num [walshTail, walsh4, spin, Fin.sum_univ_succ, Matrix.sum_apply, Matrix.zero_apply,
        Complex.star_def, Complex.conj_I]; ring

private def symmetricFourierBasis : Fin 4 → Qubit :=
  ![1, !![0, (Real.sqrt 2 : ℂ); 0, 0], !![1, 0; 0, -1], !![0, 0; (Real.sqrt 2 : ℂ), 0]]

private theorem symmetric_fourier_kraus_normalized :
    ∑ e, (qubitKraus symmetricFourierBasis e).conjTranspose *
      qubitKraus symmetricFourierBasis e = 1 := by
  have hq : (halfRoot : ℂ) ^ 2 = 1 / 2 := by
    rw [← Complex.ofReal_pow, halfRoot_sq]
    norm_num
  have hs : (halfRoot : ℂ) * (Real.sqrt 2 : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, halfRoot, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qubitKraus, symmetricFourierBasis, Matrix.sum_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Complex.star_def, hs] <;>
    ring_nf <;> norm_num [hq]

private def symmetricFourierTail (t : Fin 4 → ℝ) (j : Fin 4) : Qubit :=
  spin (t 2 * (fourier4 j 2).re)
    ((Real.sqrt 2 : ℂ) * (t 1 : ℂ) * fourier4 j 1)

/-- The symmetric Fourier family has a common attaining two-dimensional encoder. -/
theorem symmetric_fourier4_attains (t : Fin 4 → ℝ) (hr : 0 < fourierTail t)
    (hs : t 1 = t 3) :
    (t 0 + fourierTail t) ^ 2 / 4 ∈ successSet (Fin 2) (phaseVector fourier4 t) := by
  apply qubit_attainment_of_coefficients fourier4 t (fourierTail t) hr symmetricFourierBasis
    symmetric_fourier_kraus_normalized (symmetricFourierTail t)
  · intro j
    ext o e
    fin_cases j <;> fin_cases o <;> fin_cases e <;>
      norm_num [coefficient, phaseVector, symmetricFourierBasis, fourier4, symmetricFourierTail,
        spin, Fin.sum_univ_succ, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
        Complex.star_def, Complex.conj_I, Matrix.one_apply, ← hs] <;> ring
  · intro j
    exact spin_hermitian _ _
  · intro j
    exact trace_spin _ _
  · intro j
    rw [symmetricFourierTail, spin_sq]
    have hr2 : (fourierTail t) ^ 2 = t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 :=
      Real.sq_sqrt (by positivity)
    congr 1
    rw [← Complex.ofReal_pow, ← Complex.ofReal_add, ← Complex.ofReal_pow, hr2]
    congr 1
    have hsq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    fin_cases j <;>
      norm_num [fourier4, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, ← hs] <;>
      linear_combination (t 1)^2 * hsq
  · ext o e
    fin_cases o <;> fin_cases e <;>
      norm_num [symmetricFourierTail, fourier4, spin, Fin.sum_univ_succ, Matrix.sum_apply,
        Matrix.zero_apply, Complex.star_def, Complex.conj_I]

end

end PhaseMemoryOptimized
