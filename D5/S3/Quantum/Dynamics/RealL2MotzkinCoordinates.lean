/- GID: D5/S3/Quantum/Dynamics/RealL2MotzkinCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/RealL2MotzkinCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every real half-line iterate coordinate is a signed Motzkin polynomial evaluation. -/

import D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped InnerProductSpace lp
open ContinuousLinearMap
open D5.S3.Quantum.Dynamics.RealL2FirstReturnMoments
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

namespace D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates

/-- At every natural time and height, the actual half-line iterate equals the
Motzkin polynomial evaluated with both horizontal weights three, with alternating sign. -/
theorem iterate_coordinates (k j : Nat) :
    ((infiniteOperator ^ k) endpoint) j = (-1 : Real) ^ j *
      MvPolynomial.eval₂Hom (Int.castRingHom Real) (fun _ : Fin 2 => (3 : Real))
        (motzkin k j) := by
  classical
  have hsa (x : ℓ²(Nat, Real)) (j : Nat) : shift.adjoint x j = x (j + 1) := by
    have hsingle : shift (lp.single 2 j (1 : Real)) = lp.single 2 (j + 1) 1 := by
      apply lp.ext
      funext i
      cases i with
      | zero => simp [shift, lp.single_apply]
      | succ i => simp [shift, lp.single_apply, Pi.single_apply]
    have h := ContinuousLinearMap.adjoint_inner_left shift (lp.single 2 j (1 : Real)) x
    rw [hsingle, lp.inner_single_right, lp.inner_single_right] at h
    simpa using h
  have hzero (x : ℓ²(Nat, Real)) : infiniteOperator x 0 = 3 * x 0 - x 1 := by
    change 3 * x 0 - shift x 0 - shift.adjoint x 0 = _
    rw [show shift x 0 = 0 from rfl, hsa]
    ring
  have hsucc (x : ℓ²(Nat, Real)) (j : Nat) :
      infiniteOperator x (j + 1) = 3 * x (j + 1) - x j - x (j + 2) := by
    change 3 * x (j + 1) - shift x (j + 1) - shift.adjoint x (j + 1) = _
    rw [show shift x (j + 1) = x j from rfl, hsa]
  induction k generalizing j with
  | zero =>
    by_cases hj : j = 0
    · subst j
      simp [endpoint, motzkin, lp.single_apply]
    · simp [endpoint, motzkin, lp.single_apply, hj]
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    cases j with
    | zero =>
      rw [hzero, ih 0, ih 1]
      simp [motzkin, sVar]
    | succ j =>
      rw [hsucc, ih (j + 1), ih j, ih (j + 2)]
      simp only [motzkin, Nat.succ_ne_zero,
        ↓reduceIte, Nat.add_sub_cancel, map_add, map_mul, tVar,
        MvPolynomial.eval₂Hom_X', pow_succ]
      ring

#print axioms iterate_coordinates

end D5.S3.Quantum.Dynamics.RealL2MotzkinCoordinates
