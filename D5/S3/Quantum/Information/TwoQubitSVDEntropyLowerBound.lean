/- GID: D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two-qubit SVD entropy is at least the smaller input entanglement entropy. -/

import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.Schatten.TraceNorm

/-!
For two-qubit coefficient matrices, the adjugate complement identity bounds the square
of the trace of the transition's absolute value by one. After normalization, its determinant
is at least the smaller reduced-state determinant. Qubit entropy increases with this determinant.
The spectral entropy uses natural logarithms, including zero eigenvalues.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Matrix.CartesianVariance
open D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

namespace D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
open D5.S3.Quantum.Schatten.TraceNorm (transitionMass_sq det_transitionAbs)

def reducedTransition (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialTraceRight
    (Matrix.vecMulVec (Function.uncurry A) (star (Function.uncurry B)))

def reducedDensity (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialTraceRight (pureCoupling A)

def svdDensity (T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((CFC.sqrt (Tᴴ * T)).trace.re)⁻¹ • CFC.sqrt (Tᴴ * T)

def claim : Prop :=
  ∀ (A B : Matrix (Fin 2) (Fin 2) ℂ),
    RHLinalg.frobSq A = 1 → RHLinalg.frobSq B = 1 → reducedTransition A B ≠ 0 →
    min
      (spectralEntropy (partialTraceRight_posSemidef (pureCoupling_psd A)).isHermitian)
      (spectralEntropy (partialTraceRight_posSemidef (pureCoupling_psd B)).isHermitian)
      ≤ spectralEntropy
        ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg
          ((reducedTransition A B)ᴴ * reducedTransition A B))).smul
          (inv_nonneg.mpr (Complex.nonneg_iff.mp
            (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg
              ((reducedTransition A B)ᴴ * reducedTransition A B))).trace_nonneg).1)).isHermitian

private theorem reducedDensity_posSemidef (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (reducedDensity A).PosSemidef :=
  partialTraceRight_posSemidef (pureCoupling_psd A)

private theorem svdDensity_posSemidef (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (svdDensity T).PosSemidef :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Tᴴ * T))).smul
    (inv_nonneg.mpr (Complex.nonneg_iff.mp
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Tᴴ * T))).trace_nonneg).1)

private theorem reducedTransition_eq_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    reducedTransition A B = A * Bᴴ := by
  rw [reducedTransition.eq_1]
  ext i j
  simp only [partialTraceRight, Matrix.vecMulVec, Function.uncurry,
    Pi.star_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem reducedDensity_trace (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (reducedDensity A).trace = (RHLinalg.frobSq A : ℂ) := by
  rw [reducedDensity, pureCoupling,
    D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.marginal_trace,
    frobSq_eq_sum]
  simp only [Fintype.sum_prod_type, Function.uncurry, ← Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]

private theorem two_mul_norm_det_le_frobSq (C : Matrix (Fin 2) (Fin 2) ℂ) :
    2 * ‖C.det‖ ≤ RHLinalg.frobSq C := by
  have h := norm_sub_le (C 0 0 * C 1 1) (C 0 1 * C 1 0)
  rw [norm_mul, norm_mul] at h
  rw [Matrix.det_fin_two, frobSq_eq_sum]
  simp only [Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
  nlinarith only [h, sq_nonneg (‖C 0 0‖ - ‖C 1 1‖),
    sq_nonneg (‖C 0 1‖ - ‖C 1 0‖)]

private theorem frobSq_mul_conjTranspose_add_mul_adjugate
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    RHLinalg.frobSq (A * Bᴴ) + RHLinalg.frobSq (A * Matrix.adjugate B) =
      RHLinalg.frobSq A * RHLinalg.frobSq B := by
  simp only [frobSq_eq_sum, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

private theorem frobSq_mul_conjTranspose_add_two_det_le
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    RHLinalg.frobSq (A * Bᴴ) + 2 * ‖A.det‖ * ‖B.det‖ ≤
      RHLinalg.frobSq A * RHLinalg.frobSq B := by
  have h := two_mul_norm_det_le_frobSq (A * Matrix.adjugate B)
  simp only [Matrix.det_mul, Matrix.det_adjugate, Fintype.card_fin,
    Nat.reduceSub, pow_one, norm_mul] at h
  linarith [frobSq_mul_conjTranspose_add_mul_adjugate A B]

private theorem transitionMass_pos {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ≠ 0) :
    0 < (CFC.sqrt (Tᴴ * T)).trace.re := by
  have hp := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Tᴴ * T))
  have hr := Complex.nonneg_iff.mp hp.trace_nonneg
  refine lt_of_le_of_ne hr.1 ?_
  intro h
  have hz : (CFC.sqrt (Tᴴ * T)).trace = 0 := Complex.ext h.symm hr.2.symm
  have hd := hp.trace_eq_zero_iff.mp hz
  exact hT (CFC.abs_eq_zero_iff.mp hd)

private theorem svdDensity_trace {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ≠ 0) :
    (svdDensity T).trace = 1 := by
  rw [svdDensity, Matrix.trace_smul]
  have hr := (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Tᴴ * T))).trace_nonneg).2
  apply Complex.ext
  · simpa only [Complex.smul_re, smul_eq_mul, Complex.one_re] using
      inv_mul_cancel₀ (ne_of_gt (transitionMass_pos hT))
  · simp only [Complex.smul_im, hr.symm, smul_zero, Complex.one_im]

private theorem svdDensity_det (T : Matrix (Fin 2) (Fin 2) ℂ) :
    (svdDensity T).det.re = ‖T.det‖ / (CFC.sqrt (Tᴴ * T)).trace.re ^ 2 := by
  rw [svdDensity, Matrix.det_smul_of_tower, det_transitionAbs]
  simp only [Fintype.card_fin, Complex.smul_re, Complex.ofReal_re,
    smul_eq_mul, inv_pow, div_eq_mul_inv]
  ring

private theorem det_svdDensity_ge_min
    (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : RHLinalg.frobSq A = 1) (hB : RHLinalg.frobSq B = 1)
    (hT : reducedTransition A B ≠ 0) :
    min (reducedDensity A).det.re (reducedDensity B).det.re ≤
      (svdDensity (reducedTransition A B)).det.re := by
  have hdet : ‖(reducedTransition A B).det‖ = ‖A.det‖ * ‖B.det‖ := by
    rw [reducedTransition_eq_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      norm_mul, norm_star]
  have hpos : 0 < (CFC.sqrt ((reducedTransition A B)ᴴ *
      reducedTransition A B)).trace.re ^ 2 := sq_pos_of_pos (transitionMass_pos hT)
  have hmass : (CFC.sqrt ((reducedTransition A B)ᴴ *
      reducedTransition A B)).trace.re ^ 2 ≤ 1 := by
    rw [transitionMass_sq, hdet, reducedTransition_eq_mul]
    simpa only [hA, hB, one_mul, mul_assoc] using
      frobSq_mul_conjTranspose_add_two_det_le A B
  rw [svdDensity_det, hdet]
  simp only [reducedDensity, pureCoupling,
    D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.Direct.pure_det]
  rw [show Matrix.of (Function.curry (Function.uncurry A)) = A by ext i j; rfl,
    show Matrix.of (Function.curry (Function.uncurry B)) = B by ext i j; rfl]
  apply le_trans _ (le_div_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpos hmass)
  rcases le_total ‖A.det‖ ‖B.det‖ with hab | hba
  · exact (min_le_left _ _).trans (by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hab (norm_nonneg A.det))
  · exact (min_le_right _ _).trans (by
      simpa only [pow_two, mul_comm] using
        mul_le_mul_of_nonneg_left hba (norm_nonneg B.det))

private theorem binEntropy_mono_product {p q : ℝ}
    (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) (hq : q ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hprod : p * (1 - p) ≤ q * (1 - q)) : Real.binEntropy p ≤ Real.binEntropy q := by
  have hqp : q ≤ p := by
    by_contra h
    have hpq : p < q := lt_of_not_ge h
    have hsum : 0 < p + q - 1 := by linarith [hp.1]
    have hmul := mul_pos (sub_pos.mpr hpq) hsum
    nlinarith only [hprod, hmul]
  exact Real.binEntropy_strictAntiOn.antitoneOn
    (by simpa only [one_div] using hq) (by simpa only [one_div] using hp) hqp

private theorem qubit_entropy_parameter (R : Matrix (Fin 2) (Fin 2) ℂ)
    (hR : R.PosSemidef) (htr : R.trace = 1) :
    ∃ p : ℝ, p ∈ Set.Icc (1 / 2 : ℝ) 1 ∧ R.det.re = p * (1 - p) ∧
      spectralEntropy hR.isHermitian = Real.binEntropy p := by
  have hd :=
    D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.qubit_det_bounds R hR htr
  have hrad : 0 ≤ 1 - 4 * R.det.re := by
    linarith [hd.2]
  have hsq := Real.sq_sqrt hrad
  have hs := Real.sqrt_nonneg (1 - 4 * R.det.re)
  refine ⟨(1 + Real.sqrt (1 - 4 * R.det.re)) / 2, ?_, ?_, ?_⟩
  · constructor <;> nlinarith
  · nlinarith
  · have he :=
      D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.qubit_entropy_det R hR htr
    rw [D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds.S,
      dif_pos hR.isHermitian] at he
    apply (div_left_inj' (show Real.log 2 ≠ 0 by positivity)).mp
    rw [he, ← Real.binEntropy_one_sub ((1 + Real.sqrt (1 - 4 * R.det.re)) / 2)]
    convert_to
      D5.S3.Quantum.CloningMachine.binaryEntropyBits
        ((1 - Real.sqrt (1 - 4 * R.det.re)) / 2) =
      Real.binEntropy ((1 - Real.sqrt (1 - 4 * R.det.re)) / 2) / Real.log 2 using 1
    · congr 2; ring
    simp only [D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb,
      Real.binEntropy, Real.log_inv]
    ring

private theorem qubit_entropy_mono_det {R S : Matrix (Fin 2) (Fin 2) ℂ}
    (hR : R.PosSemidef) (hS : S.PosSemidef)
    (htrR : R.trace = 1) (htrS : S.trace = 1) (hdet : R.det.re ≤ S.det.re) :
    spectralEntropy hR.isHermitian ≤ spectralEntropy hS.isHermitian := by
  obtain ⟨p, hp, hdp, hep⟩ := qubit_entropy_parameter R hR htrR
  obtain ⟨q, hq, hdq, heq⟩ := qubit_entropy_parameter S hS htrS
  rw [hep, heq]
  exact binEntropy_mono_product hp hq (by simpa only [← hdp, ← hdq] using hdet)

/-- SVD entanglement entropy dominates the smaller of the two input entanglement entropies. -/
theorem result : claim := by
  intro A B hA hB hT
  have hρA := reducedDensity_posSemidef A
  have hρB := reducedDensity_posSemidef B
  have hQ := svdDensity_posSemidef (reducedTransition A B)
  have htrA : (reducedDensity A).trace = 1 := by rw [reducedDensity_trace, hA]; rfl
  have htrB : (reducedDensity B).trace = 1 := by rw [reducedDensity_trace, hB]; rfl
  have htrQ := svdDensity_trace hT
  have hd := det_svdDensity_ge_min A B hA hB hT
  change min (spectralEntropy hρA.isHermitian) (spectralEntropy hρB.isHermitian) ≤
    spectralEntropy hQ.isHermitian
  rcases le_total (reducedDensity A).det.re (reducedDensity B).det.re with hab | hba
  · rw [min_eq_left hab] at hd
    exact (min_le_left _ _).trans (qubit_entropy_mono_det hρA hQ htrA htrQ hd)
  · rw [min_eq_right hba] at hd
    exact (min_le_right _ _).trans (qubit_entropy_mono_det hρB hQ htrB htrQ hd)

end D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
