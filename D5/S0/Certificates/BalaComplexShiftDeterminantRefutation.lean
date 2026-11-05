/- GID: D5/S0/Certificates/BalaComplexShiftDeterminantRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/BalaComplexShiftDeterminantRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.claim; result=D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.result; claim=D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.claim
   digest: The one-based complex-shift determinant conjecture in OEIS A086205 fails at n = 1 and z = 1. -/

import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

/-! The arbitrary-complex-shift assertion of OEIS A086205 fails already at size one. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.BalaComplexShiftDeterminantRefutation

/-- The generalized-binomial determinant with rows and columns numbered from one. -/
noncomputable def shiftedDet (n : ℕ) (z : ℂ) : ℂ :=
  Matrix.det (fun i j : Fin n =>
    Ring.choose (((i.val + 1 : ℕ) : ℂ) ^ 2 + z) (j.val + 1))

/-- Bala's arbitrary-complex-shift conjecture, including the empty determinant. -/
def claim : Prop := ∀ (n : ℕ) (z : ℂ), shiftedDet n z = shiftedDet n 0

/-- At size one and shift one, the two determinants are two and one. -/
theorem result : ¬ claim := by
  intro h
  have hbad := h 1 1
  unfold shiftedDet at hbad
  rw [Matrix.det_fin_one, Matrix.det_fin_one] at hbad
  norm_num [Ring.choose_one_right] at hbad

end D5.S0.Certificates.BalaComplexShiftDeterminantRefutation
