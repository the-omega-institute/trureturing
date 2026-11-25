/- GID: D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/FourLevelBathObserverFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A four-outcome reference Fourier measurement enables exact one-way readout on the actual bath record. -/

import D5.S3.Quantum.Decoherence.FourLevelBathObserver
import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

/-!
# One-way Fourier readout of the actual purified bath record

The reference measurement is in the four-point Fourier basis. Its outcome is
sent to the bath observer, who uses the corresponding phase-adjusted
orthogonal projectors. These are ideal phase-sensitive measurements.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Decoherence.FourLevelBathObserver

open Matrix _root_.D5.S3.Quantum.Decoherence.FourLevelBathPhysical
open scoped BigOperators Kronecker
open D5.S3.Quantum.Dynamics.PolygonalFourierCouplings (transform transform_unitary)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

private def bathResidue : Bath ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv

/-- Fourier eigenvectors in the reference coordinates. The column is indexed
by the single four-valued outcome to be communicated. -/
def referenceFourier : Matrix Bath Bath ℂ :=
  (transform 4).submatrix bathResidue bathResidue

private def fourierCharacter (b k : Bath) : ℂ :=
  ZMod.stdAddChar (-(bathResidue b * bathResidue k))

private theorem referenceFourier_entry (b k : Bath) :
    referenceFourier b k = (1 / 2 : ℂ) * fourierCharacter b k := by
  change fourierCharacter b k / (Real.sqrt (4 : ℝ) : ℂ) = _
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    calc
      Real.sqrt (4 : ℝ) = Real.sqrt (2 ^ 2) := by norm_num
      _ = 2 := Real.sqrt_sq (by norm_num)
  rw [hs, Complex.ofReal_ofNat, div_eq_mul_inv, one_div, mul_comm]

private theorem referenceFourier_mul_adjoint : referenceFourier * referenceFourierᴴ = 1 := by
  rw [referenceFourier, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ bathResidue _, transform_unitary, Matrix.submatrix_one_equiv]

private theorem referenceFourier_isometry : referenceFourierᴴ * referenceFourier = 1 :=
  mul_eq_one_comm.mp referenceFourier_mul_adjoint

/-- The actual Fourier basis projectors for R. -/
def referenceEffect (k : Bath) : Matrix Bath Bath ℂ :=
  orthogonalReadout referenceFourier (some k)

theorem referenceEffect_projection (k : Bath) : IsStarProjection (referenceEffect k) :=
  orthogonalReadout_projection referenceFourier referenceFourier_isometry (some k)

theorem referenceEffect_complete : (∑ k, referenceEffect k) = 1 := by
  have h := orthogonalReadout_complete referenceFourier
  rw [Fintype.sum_option] at h
  change (1 - referenceFourier * referenceFourierᴴ) + (∑ k, referenceEffect k) = 1 at h
  simpa only [referenceFourier_mul_adjoint, sub_self, zero_add] using h

/-- The partial inner product `I_B ⊗ ⟨f_k|` for outcome k. -/
def fourierAnalysis (k : Bath) : Matrix Bath BathReference ℂ :=
  fun b x => (1 : Matrix Bath Bath ℂ) b x.1 * star (referenceFourier x.2 k)

theorem fourierAnalysis_effect (k : Bath) :
    (fourierAnalysis k)ᴴ * fourierAnalysis k =
      (1 : Matrix Bath Bath ℂ) ⊗ₖ referenceEffect k := by
  apply Matrix.ext
  rintro ⟨b, r⟩ ⟨c, s⟩
  change (∑ a : Bath, star (fourierAnalysis k a (b, r)) * fourierAnalysis k a (c, s)) =
    (1 : Matrix Bath Bath ℂ) b c *
      (referenceFourier r k * star (referenceFourier s k))
  rw [Finset.sum_eq_single b]
  · simp [fourierAnalysis, star_mul] <;> ring
  · intro a _ ha
    simp [fourierAnalysis, Matrix.one_apply, ha]
  · simp

/-- The normalized bath columns for the conditional measurement following k. -/
def fourierColumns (p : Bath → ℝ) (z : Bath → System → ℂ) (k : Bath) :
    Matrix Bath System ℂ :=
  Matrix.diagonal (fun b => star (fourierCharacter b k)) * weightedColumns p z

theorem fourierColumns_isometry (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (k : Bath) :
    (fourierColumns p z k)ᴴ * fourierColumns p z k = 1 := by
  let D : Matrix Bath Bath ℂ := Matrix.diagonal (fun b => star (fourierCharacter b k))
  have hD : Dᴴ * D = 1 := by
    dsimp only [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    apply Matrix.diagonal_eq_one.mpr
    funext b
    change star (star (fourierCharacter b k)) * star (fourierCharacter b k) = 1
    rw [star_star, Complex.star_def, Complex.mul_conj]
    simp [fourierCharacter, ZMod.stdAddChar_apply]
  change (D * weightedColumns p z)ᴴ * (D * weightedColumns p z) = 1
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Dᴴ D, hD,
    Matrix.one_mul, hGram]

private theorem fourierAnalysis_record (p : Bath → ℝ) (z : Bath → System → ℂ)
    (i : System) (k : Bath) :
    fourierAnalysis k *ᵥ recordVector p z i =
      (1 / 2 : ℂ) • (fun b => fourierColumns p z k b i) := by
  funext b
  change (∑ x : BathReference, fourierAnalysis k b x * recordVector p z i x) =
    (1 / 2 : ℂ) * fourierColumns p z k b i
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single b]
    · simp [fourierAnalysis, recordVector, correlatedVector, referenceFourier_entry,
        fourierColumns, Matrix.diagonal_mul, star_mul, Complex.star_def]
      <;> ring
    · intro r _ hr
      simp [recordVector, correlatedVector, Ne.symm hr]
    · simp
  · intro a _ ha
    simp [fourierAnalysis, Matrix.one_apply, Ne.symm ha]
  · simp

/-- The actual subnormalized bath output of the reference measurement. -/
def fourierBranch (p : Bath → ℝ) (U : Joint) (i : System) (k : Bath) : Matrix Bath Bath ℂ :=
  fourierAnalysis k * conditionalRecord p U i * (fourierAnalysis k)ᴴ

theorem fourierBranch_eq (p : Bath → ℝ) (z : Bath → System → ℂ) (i : System) (k : Bath) :
    fourierBranch p (phaseUnitary z) i k =
      ((1 / 4 : ℝ) : ℂ) • rankOneDensity (fun b => fourierColumns p z k b i) := by
  rw [fourierBranch, conditionalRecord_eq]
  simp only [rankOneDensity, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
    fourierAnalysis_record]
  apply Matrix.ext
  intro b c
  simp [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
    star_mul, Complex.star_def, Complex.ofReal_div]
  <;> ring

private theorem trace_reference_effect (E : Matrix Bath Bath ℂ)
    (A : Matrix BathReference BathReference ℂ) :
    (Matrix.trace (((1 : Matrix Bath Bath ℂ) ⊗ₖ E) * A)) =
      (Matrix.trace (E * partialTraceLeft A)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, partialTraceLeft]
  calc
    _ = ∑ a : Bath, ∑ b : Bath, ∑ c : Bath, E b c * A (a, c) (a, b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single a]
      · simp
      · intro a' _ ha
        simp [Ne.symm ha]
      · simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

theorem fourier_outcome_uniform (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1) (i : System) (k : Bath) :
    (Matrix.trace (referenceEffect k *
      partialTraceLeft (conditionalRecord p (phaseUnitary z) i))).re = 1 / 4 := by
  have hV := fourierColumns_isometry p z hGram k
  have htrace : (rankOneDensity (fun b => fourierColumns p z k b i)).trace = 1 := by
    rw [rankOneDensity, Matrix.trace_vecMulVec, dotProduct_comm]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      dotProduct, Pi.star_apply] using
      congrArg (fun M : Qutrit => M i i) hV
  have hbranch : (fourierBranch p (phaseUnitary z) i k).trace =
      ((1 / 4 : ℝ) : ℂ) := by
    rw [fourierBranch_eq, Matrix.trace_smul, htrace, smul_eq_mul, mul_one]
  have hlaw :
      (fourierBranch p (phaseUnitary z) i k).trace =
        (referenceEffect k *
          partialTraceLeft (conditionalRecord p (phaseUnitary z) i)).trace := by
    rw [fourierBranch, Matrix.trace_mul_cycle, fourierAnalysis_effect]
    exact trace_reference_effect _ _
  rw [← hlaw, hbranch, Complex.ofReal_re]

/-- The sequential Born law on the physical output. The first observer sends k
and the bath observer uses the orthogonal readout built from the k-dependent
columns. The correct label has conditional probability one for every k. -/
theorem fourier_decoder_born (p : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1)
    (i : System) (k : Bath) (o : Option System) :
    (Matrix.trace (orthogonalReadout (fourierColumns p z k) o *
      fourierBranch p (phaseUnitary z) i k)).re = if o = some i then 1 / 4 else 0 := by
  rw [fourierBranch_eq, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    orthogonalReadout_born _ (fourierColumns_isometry p z hGram k)]
  split_ifs <;> simp

end D5.S3.Quantum.Decoherence.FourLevelBathObserver
