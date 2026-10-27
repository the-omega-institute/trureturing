/- GID: D5/S3/Quantum/Recovery/BurriReverseOverlap
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReverseOverlap
   mirror-E: none(waiver:unfinished-petz-and-source-identifications)
   anchors: []
   utility: none
   digest: Canonical purified overlaps of the literal reverse-instance Kraus maps. -/

import D5.S3.Quantum.Recovery.BurriReversePolar
import D5.S3.Quantum.QuantumChannels.MayerZeroFidelityTightness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Recovery.BurriReverseDecoder
open D5.S3.Quantum.Recovery.BurriReversePolar
open D5.S3.QuantumBounds.PeritoTsirelson
open D5.S3.Quantum.PureState.PureStateHandshake

namespace D5.S3.Quantum.Recovery.BurriReverseOverlap

/-- Only a reindexing of the two full source-environment Kraus labels. -/
def labels : Fin (Fintype.card (E × E)) ≃ E × E := (Fintype.equivFin (E × E)).symm
def composite (D : E → Matrix A B ℂ) (p : E × E) : Matrix A A ℂ :=
  D p.1 * noiseKraus p.2
def amplified (D : E → Matrix A B ℂ) (j : Fin (Fintype.card (E × E))) :
    Matrix (A × A) (A × A) ℂ :=
  Matrix.kronecker (composite D (labels j)) (1 : Matrix A A ℂ)

/-- The actual composite Kraus map applied to the canonical maximally mixed purification. -/
def recoveredPurification (D : E → Matrix A B ℂ) : Matrix (A × A) (A × A) ℂ :=
  MatrixMap.of_kraus (amplified D) (amplified D) (maxEntangled A)
def fidelity (D : E → Matrix A B ℂ) : ℝ :=
  (star (maxEntangledVector A) ⬝ᵥ recoveredPurification D *ᵥ maxEntangledVector A).re

theorem purification_overlap (D : E → Matrix A B ℂ) :
    fidelity D = ∑ p : E × E, Complex.normSq (Matrix.trace (composite D p) / 2) := by
  have hamplitude (j : Fin (Fintype.card (E × E))) :
      star (maxEntangledVector A) ⬝ᵥ amplified D j *ᵥ maxEntangledVector A =
        Matrix.trace (composite D (labels j)) / 2 := by
    calc
      _ = Matrix.trace (maxEntangled A * amplified D j) := by
        rw [maxEntangled.eq_1, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
          Matrix.dotProduct_mulVec, dotProduct_comm]
      _ = _ := by
        rw [amplified, Matrix.kronecker, max_entangled_trace, Matrix.mul_one,
          Matrix.trace_transpose, Fintype.card_fin]
  unfold fidelity recoveredPurification
  rw [maxEntangled.eq_1]
  change (star (maxEntangledVector A) ⬝ᵥ
    MatrixMap.of_kraus (amplified D) (amplified D)
      (rankOneDensity (maxEntangledVector A)) *ᵥ maxEntangledVector A).re = _
  rw [D5.S3.Quantum.QuantumChannels.MayerZeroFidelityTightness.kraus_survival]
  simp_rw [hamplitude, ← Complex.normSq_eq_norm_sq]
  exact labels.sum_comp (fun p => Complex.normSq (Matrix.trace (composite D p) / 2))

set_option maxHeartbeats 2000000 in
-- The full twelve-by-twelve label sum has only three nonzero trace overlaps.
theorem source_overlap (cp cm kp km : ℝ) :
    fidelity (swKraus cp cm kp km) =
      ((4 * cp + 2 * cm + kp + km) ^ 2 + 36 +
        (3 * cp + 3 * cm - (kp + km)) ^ 2) / 124 := by
  have hs : Real.sqrt 31 ^ 2 = 31 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 31 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [purification_overlap]
  norm_num [composite, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    supported_rows, noiseKraus, V, active, activeU, BurriReverseDecoder.rotation, Y, amplitude, sign,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Complex.normSq, Complex.div_re, Complex.div_im]
  field_simp
  nlinarith

set_option maxHeartbeats 2000000 in
-- Environment slices give the second actual purified Kraus overlap.
theorem slice_overlap : fidelity slice = 27 / 31 := by
  have hs : Real.sqrt 31 ^ 2 = 31 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 31 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [purification_overlap]
  norm_num [composite, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    slice, noiseKraus, V, active, Y, amplitude, sign,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three,
    Complex.normSq, Complex.div_re, Complex.div_im]
  field_simp
  nlinarith

set_option maxHeartbeats 2000000 in
-- The full source-label Gram matrix is the active unitary Gram matrix.
theorem source_normalization (cp cm kp km : ℝ)
    (hp : cp ^ 2 + kp ^ 2 = 1) (hm : cm ^ 2 + km ^ 2 = 1) :
    (∑ e : E, (swKraus cp cm kp km e)ᴴ * swKraus cp cm kp km e) = 1 := by
  have hu := (rotation_unitary cp cm kp km hp hm).1
  ext b c
  have h := congrFun (congrFun hu b) c
  simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    supported_rows, active, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, add_assoc, add_left_comm, add_comm] using h

theorem slice_normalization : (∑ e : E, (slice e)ᴴ * slice e) = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases a <;> fin_cases j <;> fin_cases b <;>
    norm_num [slice, active, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]

/-- Both recovery constructions define genuine channels on the full physical output. -/
theorem recovery_channels :
    (∃ channel : QuantumChannel B A, ∀ T : Matrix B B ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
        ∑ e : E, swKraus (cosine 4) (cosine 2) (sine 4) (sine 2) e * T *
          (swKraus (cosine 4) (cosine 2) (sine 4) (sine 2) e)ᴴ) ∧
    (∃ channel : QuantumChannel B A, ∀ T : Matrix B B ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
        ∑ e : E, slice e * T * (slice e)ᴴ) := by
  exact ⟨finite_kraus_quantum_channel _
    (source_normalization _ _ _ _ (parameters 4).1 (parameters 2).1),
    finite_kraus_quantum_channel slice slice_normalization⟩

/-- Strict comparison of the two specified purified Kraus overlaps.
Identifying the slice map as ordinary Petz is a separate obligation. -/
theorem canonical_overlap_gap :
    fidelity (swKraus (cosine 4) (cosine 2) (sine 4) (sine 2)) < fidelity slice := by
  rw [source_overlap, slice_overlap]
  linarith [actual_polynomial_gap]

#print axioms purification_overlap
#print axioms source_overlap
#print axioms slice_overlap
#print axioms canonical_overlap_gap
#print axioms recovery_channels

end D5.S3.Quantum.Recovery.BurriReverseOverlap
