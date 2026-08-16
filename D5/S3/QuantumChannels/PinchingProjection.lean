/- GID: D5/S3/QuantumChannels/PinchingProjection
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pinching is an HS-orthogonal projection with exact discarded coherence mass. -/

import Mathlib
import D5.S3.QuantumChannels.Pinching

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT
Mathlib layer:
* Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Idempotent.lean:13-24 studies
  `IsIdempotentElem` for continuous linear endomorphisms, not bare functions.
* Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:155-178 gives the standard
  orthogonality characterization, and lines 545-554 give its Pythagorean theorem; both require
  an `InnerProductSpace`, a submodule, and `HasOrthogonalProjection`.
* Mathlib/Analysis/InnerProductSpace/Basic.lean:243-247 and 412-414 provide the standard inner
  subtraction and real norm-square expansions, again through the built-in inner-product API.
* Mathlib/Data/Complex/Basic.lean:517-545 identifies `Complex.normSq` with conjugate times self.
Repository layer:
* D5/S3/Quantum/FiniteDimensional.lean:14-15 defines `QubitMatrix` as a `Fin 2` complex matrix.
* D5/S3/QuantumChannels/Pinching.lean:16-21 defines `pinching` and the custom trace-based HS
  product; lines 25-38 provide `pinching_apply`, idempotence, and HS self-adjointness.
Verdict: the mathlib projection theorems do not directly apply to this bare function and custom
inner product.  Reuse the two frozen pinching laws, with only local HS additivity and the `Fin 2`
entry computation proved below.
-/

namespace D5.S3.QuantumChannels.PinchingProjection

open D5.S3.Quantum.FiniteDimensional
open D5.S3.QuantumChannels.Pinching

private theorem hilbert_schmidt_add_left (A B C : QubitMatrix) :
    hilbertSchmidtInner (A + B) C =
      hilbertSchmidtInner A C + hilbertSchmidtInner B C := by
  simp [hilbertSchmidtInner, Matrix.add_mul]

private theorem hilbert_schmidt_add_right (A B C : QubitMatrix) :
    hilbertSchmidtInner A (B + C) =
      hilbertSchmidtInner A B + hilbertSchmidtInner A C := by
  simp [hilbertSchmidtInner, Matrix.mul_add]

/-- The pinched component is Hilbert-Schmidt orthogonal to the discarded component. -/
theorem pinching_hilbert_schmidt_orthogonal (rho : QubitMatrix) :
    hilbertSchmidtInner (pinching rho) (rho - pinching rho) = 0 := by
  have hIdem : pinching (pinching rho) = pinching rho :=
    congrFun pinching_idempotent rho
  have hInner :
      hilbertSchmidtInner (pinching rho) rho =
        hilbertSchmidtInner (pinching rho) (pinching rho) := by
    calc
      hilbertSchmidtInner (pinching rho) rho =
          hilbertSchmidtInner (pinching (pinching rho)) rho := by rw [hIdem]
      _ = hilbertSchmidtInner (pinching rho) (pinching rho) :=
        pinching_hilbert_schmidt_self_adjoint (pinching rho) rho
  calc
    hilbertSchmidtInner (pinching rho) (rho - pinching rho) =
        hilbertSchmidtInner (pinching rho) rho -
          hilbertSchmidtInner (pinching rho) (pinching rho) := by
      simp [hilbertSchmidtInner, Matrix.mul_sub]
    _ = 0 := sub_eq_zero.mpr hInner

/-- Pinching splits Hilbert-Schmidt mass into diagonal and discarded-coherence mass. -/
theorem pinching_hilbert_schmidt_pythagorean (rho : QubitMatrix) :
    hilbertSchmidtInner rho rho =
      hilbertSchmidtInner (pinching rho) (pinching rho) +
        hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho) := by
  let discarded := rho - pinching rho
  have hDecomp : rho = pinching rho + discarded := by
    dsimp [discarded]
    abel
  have hDiscardedPinching : pinching discarded = 0 := by
    ext i j
    by_cases h : i = j <;> simp [discarded, h]
  have hReverseOrthogonal : hilbertSchmidtInner discarded (pinching rho) = 0 := by
    calc
      hilbertSchmidtInner discarded (pinching rho) =
          hilbertSchmidtInner (pinching discarded) rho :=
        (pinching_hilbert_schmidt_self_adjoint discarded rho).symm
      _ = 0 := by simp [hDiscardedPinching, hilbertSchmidtInner]
  calc
    hilbertSchmidtInner rho rho =
        hilbertSchmidtInner (pinching rho + discarded) (pinching rho + discarded) := by
      exact congrArg (fun A => hilbertSchmidtInner A A) hDecomp
    _ = (hilbertSchmidtInner (pinching rho) (pinching rho) +
          hilbertSchmidtInner (pinching rho) discarded) +
        (hilbertSchmidtInner discarded (pinching rho) +
          hilbertSchmidtInner discarded discarded) := by
      rw [hilbert_schmidt_add_left, hilbert_schmidt_add_right,
        hilbert_schmidt_add_right]
    _ = hilbertSchmidtInner (pinching rho) (pinching rho) +
        hilbertSchmidtInner discarded discarded := by
      rw [pinching_hilbert_schmidt_orthogonal, hReverseOrthogonal]
      ring
    _ = hilbertSchmidtInner (pinching rho) (pinching rho) +
        hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho) := by
      rfl

/-- For a qubit, the mass discarded by pinching is exactly the two off-diagonal norm squares. -/
theorem pinching_discarded_coherence_mass (rho : QubitMatrix) :
    hilbertSchmidtInner (rho - pinching rho) (rho - pinching rho) =
      Complex.normSq (rho 0 1) + Complex.normSq (rho 1 0) := by
  simp [hilbertSchmidtInner, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.normSq_eq_conj_mul_self]
  ring

#print axioms pinching_hilbert_schmidt_orthogonal
#print axioms pinching_hilbert_schmidt_pythagorean
#print axioms pinching_discarded_coherence_mass

end D5.S3.QuantumChannels.PinchingProjection
