/- GID: D5/S3/Quantum/Pinching
   generality: G
   mirror-B: D5/B/S3/Quantum/Pinching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize standard-basis qubit pinching as zero-retention phase damping. -/

import D5.S3.Quantum.QubitWitnesses

namespace D5.S3.Quantum.Pinching

open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses

/-- Standard-basis qubit pinching is phase damping with zero coherence retention. -/
def pinching (rho : QubitMatrix) : QubitMatrix :=
  phaseDamping (⟨0, by constructor <;> norm_num⟩ : DampingCoefficient) rho

/-- The Hilbert-Schmidt inner product, expressed through the matrix trace. -/
def hilbertSchmidtInner (A B : QubitMatrix) : ℂ :=
  Matrix.trace (Matrix.conjTranspose A * B)

/-- Pinching preserves diagonal entries and annihilates every off-diagonal entry. -/
@[simp]
theorem pinching_apply (rho : QubitMatrix) (i j : Fin 2) :
    pinching rho i j = if i = j then rho i j else 0 := by
  simp [pinching, phaseDamping]

/-- Standard-basis pinching is idempotent. -/
theorem pinching_idempotent : Function.comp pinching pinching = pinching := by
  funext rho i j
  by_cases h : i = j <;> simp [Function.comp_apply, h]

/-- Standard-basis pinching is self-adjoint for the Hilbert-Schmidt inner product. -/
theorem pinching_hilbert_schmidt_self_adjoint (A B : QubitMatrix) :
    hilbertSchmidtInner (pinching A) B = hilbertSchmidtInner A (pinching B) := by
  simp [hilbertSchmidtInner, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- Forcing test: an output entry vanishes exactly off the diagonal or when its input vanishes. -/
theorem pinching_entry_eq_zero_iff (rho : QubitMatrix) (i j : Fin 2) :
    pinching rho i j = 0 ↔ i ≠ j ∨ rho i j = 0 := by
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- Forcing test: pinching annihilates the purely off-diagonal Pauli `X`, while `X` itself
carries nonzero Hilbert-Schmidt norm. Any retention of off-diagonal weight makes the first
conjunct false, so this separates pinching from every map that only attenuates coherence. -/
theorem pinching_annihilates_offdiagonal :
    hilbertSchmidtInner (pinching qubitX) qubitX = 0 ∧
      hilbertSchmidtInner qubitX qubitX ≠ 0 := by
  constructor
  · simp [hilbertSchmidtInner, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, qubitX]
  · simp [hilbertSchmidtInner, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, qubitX]

end D5.S3.Quantum.Pinching
