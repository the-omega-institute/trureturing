/- GID: D5/S3/Observer/AgencyHolonomy/LocalEulerTransitionNonreconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/LocalEulerTransitionNonreconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local Euler determinants forget cross-address frame transitions. -/

import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Tactic

/- Library-search audit trail (2026-08-31):
   * `rg -n "Nat\\.Primes" D5 --glob '*.lean'` found `Nat.Primes` as D5's
     canonical prime index carrier. In particular, sibling Euler/prime modules
     `PrimeChannelLogEvidence` and `PrimeFactorCountMoments` use it directly,
     and the former names the two smallest primes with `Nat.prime_two` and
     `Nat.prime_three`.
   * D5 searches for transition maps, isospectral frame changes, determinant
     conjugation, and prime-indexed general-linear frames found no theorem
     exposing this non-reconstruction statement.
   * Pinned Mathlib supplies `Matrix.det_units_conj`, `Matrix.det_fin_two`, and
     `Matrix.GeneralLinearGroup.swap`; these are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.LocalEulerTransitionNonreconstruction

open Matrix

noncomputable section

/-- On the two-branch complex observer space indexed by the canonical prime
carrier `Nat.Primes`, all local Euler determinants can agree for two frame
families even though their transition between primes differs. We choose the two
smallest primes, `p2 = 2` and `p3 = 3`, and read the transition from `p2` to
`p3` as `(frame p3)⁻¹ * frame p2`. The diagonal local operators have the two
source eigenvalues `1` and `chi p`. -/
theorem local_euler_determinants_do_not_determine_transition
    (chi : Nat.Primes -> Complex) :
    let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    let p3 : Nat.Primes := ⟨3, Nat.prime_three⟩
    let localOperator : Nat.Primes -> Matrix (Fin 2) (Fin 2) Complex :=
      fun p => Matrix.diagonal fun branch => if branch = 0 then 1 else chi p
    exists firstFrame secondFrame : Nat.Primes -> GL (Fin 2) Complex,
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
      (firstFrame p3)⁻¹ * firstFrame p2 ≠
        (secondFrame p3)⁻¹ * secondFrame p2 := by
  classical
  dsimp only
  let swapFrame : GL (Fin 2) Complex :=
    Matrix.GeneralLinearGroup.swap Complex 0 1
  let firstFrame : Nat.Primes -> GL (Fin 2) Complex := fun _ => 1
  let secondFrame : Nat.Primes -> GL (Fin 2) Complex := fun p =>
    if p.1 = 2 then swapFrame else 1
  have framedDeterminant
      (frame : GL (Fin 2) Complex) (p : Nat.Primes) (x : Complex) :
      Matrix.det
          (1 - x • (frame.val *
            (Matrix.diagonal fun branch : Fin 2 => if branch = 0 then 1 else chi p) *
            (frame⁻¹).val)) =
        (1 - x) * (1 - x * chi p) := by
    let branchOperator : Matrix (Fin 2) (Fin 2) Complex :=
      Matrix.diagonal fun branch => if branch = 0 then 1 else chi p
    have conjugatedDifference :
        1 - x • (frame.val * branchOperator * (frame⁻¹).val) =
          frame.val * (1 - x • branchOperator) * (frame⁻¹).val := by
      calc
        1 - x • (frame.val * branchOperator * (frame⁻¹).val) =
            frame.val * (frame⁻¹).val -
              frame.val * (x • branchOperator) * (frame⁻¹).val := by simp
        _ = frame.val * (1 - x • branchOperator) * (frame⁻¹).val := by
          rw [mul_sub, sub_mul, mul_one]
    change Matrix.det
        (1 - x • (frame.val * branchOperator * (frame⁻¹).val)) = _
    rw [conjugatedDifference, Matrix.det_units_conj]
    simp [branchOperator, Matrix.det_fin_two]
  refine ⟨firstFrame, secondFrame, ?_, ?_, ?_⟩
  · exact fun p x => framedDeterminant (firstFrame p) p x
  · exact fun p x => framedDeterminant (secondFrame p) p x
  · simp [firstFrame, secondFrame, swapFrame,
      Matrix.GeneralLinearGroup.ext_iff, Matrix.GeneralLinearGroup.swap,
      Matrix.swap]

#print axioms local_euler_determinants_do_not_determine_transition

end

end D5.S3.Observer.AgencyHolonomy.LocalEulerTransitionNonreconstruction
