/- GID: D5/S3/Observer/AgencyHolonomy/LocalEulerTransitionNonreconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/LocalEulerTransitionNonreconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local Euler determinants forget cross-address frame transitions. -/

import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Tactic

/- Library-search audit trail (2026-08-31):
   * D5 searches for transition maps, isospectral frame changes, and determinant
     conjugation found no theorem exposing this two-branch non-reconstruction
     statement. Related observer holonomy modules use different scalar carriers.
   * D5 body-shape searches for diagonal two-branch operators, prime-indexed
     general-linear frames, and inverse-frame products found no matching owner.
   * Pinned Mathlib supplies `Matrix.det_units_conj`, `Matrix.det_fin_two`, and
     `Matrix.GeneralLinearGroup.swap`; these are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.LocalEulerTransitionNonreconstruction

open Matrix

noncomputable section

/-- On the two-branch complex observer space, all local Euler determinants can
agree for two frame families even though their transition from address zero to
address one is different. The diagonal local operators are constructed from
the two source eigenvalues `1` and `chi p`. -/
theorem local_euler_determinants_do_not_determine_transition
    (chi : Fin 2 -> Complex) :
    let localOperator : Fin 2 -> Matrix (Fin 2) (Fin 2) Complex :=
      fun p => Matrix.diagonal fun branch => if branch = 0 then 1 else chi p
    exists firstFrame secondFrame : Fin 2 -> GL (Fin 2) Complex,
      (forall p x,
        Matrix.det
            (1 - x •
              ((firstFrame p).val * localOperator p * ((firstFrame p)⁻¹).val)) =
          (1 - x) * (1 - x * chi p)) /\
      (forall p x,
        Matrix.det
            (1 - x •
              ((secondFrame p).val * localOperator p * ((secondFrame p)⁻¹).val)) =
          (1 - x) * (1 - x * chi p)) /\
      (firstFrame 1)⁻¹ * firstFrame 0 ≠
        (secondFrame 1)⁻¹ * secondFrame 0 := by
  classical
  dsimp only
  let swapFrame : GL (Fin 2) Complex :=
    Matrix.GeneralLinearGroup.swap Complex 0 1
  let firstFrame : Fin 2 -> GL (Fin 2) Complex := fun _ => 1
  let secondFrame : Fin 2 -> GL (Fin 2) Complex := fun p =>
    if p = 0 then 1 else swapFrame
  refine ⟨firstFrame, secondFrame, ?_, ?_, ?_⟩
  · intro p x
    simp [firstFrame, Matrix.det_fin_two]
  · intro p x
    fin_cases p
    · simp [secondFrame, Matrix.det_fin_two]
    · let branchOperator : Matrix (Fin 2) (Fin 2) Complex :=
        Matrix.diagonal fun branch => if branch = 0 then 1 else chi 1
      have conjugatedDifference :
          1 - x • (swapFrame.val * branchOperator * (swapFrame⁻¹).val) =
            swapFrame.val * (1 - x • branchOperator) * (swapFrame⁻¹).val := by
        calc
          1 - x • (swapFrame.val * branchOperator * (swapFrame⁻¹).val) =
              swapFrame.val * (swapFrame⁻¹).val -
                swapFrame.val * (x • branchOperator) * (swapFrame⁻¹).val := by simp
          _ = swapFrame.val * (1 - x • branchOperator) * (swapFrame⁻¹).val := by
            rw [mul_sub, sub_mul, mul_one]
      change Matrix.det
          (1 - x • (swapFrame.val * branchOperator * (swapFrame⁻¹).val)) = _
      rw [conjugatedDifference, Matrix.det_units_conj]
      simp [branchOperator, Matrix.det_fin_two]
  · simp [firstFrame, secondFrame, swapFrame,
      Matrix.GeneralLinearGroup.ext_iff, Matrix.GeneralLinearGroup.swap,
      Matrix.swap]

#print axioms local_euler_determinants_do_not_determine_transition

end

end D5.S3.Observer.AgencyHolonomy.LocalEulerTransitionNonreconstruction
