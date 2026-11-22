/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferTracePowers
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformTransferTracePowers
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Trace powers of the transfer operator compute the periodic Gram contractions. -/
import D5.S0.Observation.MatrixTracePowerSum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Four power traces of the trace-aligned mixed transfer

Each binary word contributes the product of its trace on the two
independent cores. Cyclic rotation reduces the fourth power to six word
classes.
The resulting power traces supply the order-four Newton identities for
the characteristic polynomial.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferTracePowers

open D5.S0.Observation.MatrixTracePowerSum (pow_add_two trace_pow_add_two)
open scoped Kronecker

variable {R : Type*} [CommRing R]

private abbrev BondMatrix (R : Type*) := Matrix (Fin 2) (Fin 2) R

section CyclicWords

variable {ι : Type*} [Fintype ι]

private theorem trace_rotate_three (A B C : Matrix ι ι R) :
    (A * B * C).trace = (C * A * B).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (A * B) C

private theorem trace_rotate_four (A B C D : Matrix ι ι R) :
    (A * B * C * D).trace = (D * A * B * C).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (A * B * C) D

variable [DecidableEq ι]

private theorem trace_add_sq (P Q : Matrix ι ι R) :
    ((P + Q) ^ 2).trace =
      (P * P).trace + 2 * (P * Q).trace + (Q * Q).trace := by
  simp only [pow_two, add_mul, mul_add, Matrix.trace_add, Matrix.trace_mul_comm Q P]
  ring

private theorem trace_add_cube (P Q : Matrix ι ι R) :
    ((P + Q) ^ 3).trace =
      (P * P * P).trace + 3 * (P * P * Q).trace +
        3 * (P * Q * Q).trace + (Q * Q * Q).trace := by
  simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add, Matrix.trace_add,
    trace_rotate_three P Q P, trace_rotate_three Q P P,
    trace_rotate_three Q Q P, trace_rotate_three Q P Q]
  ring

private theorem trace_add_fourth (P Q : Matrix ι ι R) :
    ((P + Q) ^ 4).trace =
      (P * P * P * P).trace + 4 * (P * P * P * Q).trace +
        4 * (P * P * Q * Q).trace + 2 * (P * Q * P * Q).trace +
        4 * (P * Q * Q * Q).trace + (Q * Q * Q * Q).trace := by
  simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add, Matrix.trace_add,
    trace_rotate_four P P Q P, trace_rotate_four P Q P P, trace_rotate_four Q P P P,
    trace_rotate_four P Q Q P, trace_rotate_four Q Q P P, trace_rotate_four Q P P Q,
    trace_rotate_four Q P Q P,
    trace_rotate_four Q Q Q P, trace_rotate_four Q Q P Q, trace_rotate_four Q P Q Q]
  ring

end CyclicWords

private theorem trace_square (M : BondMatrix R) :
    (M * M).trace = M.trace ^ 2 - 2 * M.det := by
  have h := trace_pow_add_two M 0
  change (M ^ 2).trace = M.trace * (M ^ 1).trace - M.det * (M ^ 0).trace at h
  rw [pow_two, pow_one, pow_zero, Matrix.trace_one] at h
  norm_num [Fintype.card_fin] at h
  calc
    (M * M).trace = M.trace * M.trace - M.det * 2 := h
    _ = M.trace ^ 2 - 2 * M.det := by ring

private theorem trace_cube (M : BondMatrix R) :
    (M * M * M).trace = M.trace ^ 3 - 3 * M.trace * M.det := by
  have h := trace_pow_add_two M 1
  change (M ^ 3).trace = M.trace * (M ^ 2).trace - M.det * (M ^ 1).trace at h
  simp only [pow_succ, pow_zero, one_mul] at h
  rw [trace_square] at h
  calc
    (M * M * M).trace = M.trace * (M.trace ^ 2 - 2 * M.det) - M.det * M.trace := h
    _ = M.trace ^ 3 - 3 * M.trace * M.det := by ring

private theorem trace_fourth (M : BondMatrix R) :
    (M * M * M * M).trace =
      M.trace ^ 4 - 4 * M.trace ^ 2 * M.det + 2 * M.det ^ 2 := by
  have h := trace_pow_add_two M 2
  change (M ^ 4).trace = M.trace * (M ^ 3).trace - M.det * (M ^ 2).trace at h
  simp only [pow_succ, pow_zero, one_mul] at h
  rw [trace_cube, trace_square] at h
  calc
    (M * M * M * M).trace =
        M.trace * (M.trace ^ 3 - 3 * M.trace * M.det) -
          M.det * (M.trace ^ 2 - 2 * M.det) := h
    _ = M.trace ^ 4 - 4 * M.trace ^ 2 * M.det + 2 * M.det ^ 2 := by ring

private theorem square_trace_one (A : BondMatrix R) (hA : A.trace = 1) :
    A * A = A - A.det • (1 : BondMatrix R) := by
  simpa only [Nat.zero_add, pow_two, pow_one, pow_zero, hA, one_smul] using pow_add_two A 0

private theorem square_trace_zero (B : BondMatrix R) (hB : B.trace = 0) :
    B * B = -(B.det • (1 : BondMatrix R)) := by
  simpa only [Nat.zero_add, pow_two, pow_zero, hB, zero_smul, zero_sub] using pow_add_two B 0

private theorem trace_AAB (A B : BondMatrix R) (hA : A.trace = 1) (hB : B.trace = 0) :
    (A * A * B).trace = (A * B).trace := by
  rw [square_trace_one A hA, Matrix.sub_mul, Matrix.smul_mul, one_mul,
    Matrix.trace_sub, Matrix.trace_smul, hB, smul_zero, sub_zero]

private theorem trace_ABB (A B : BondMatrix R) (hB : B.trace = 0) :
    (A * B * B).trace = -B.det * A.trace := by
  rw [Matrix.mul_assoc, square_trace_zero B hB, Matrix.mul_neg, Matrix.mul_smul, mul_one,
    Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, neg_mul]

private theorem trace_AAAB (A B : BondMatrix R) (hA : A.trace = 1) (hB : B.trace = 0) :
    (A * A * A * B).trace = (1 - A.det) * (A * B).trace := by
  rw [Matrix.mul_assoc (A * A) A B, square_trace_one A hA, Matrix.sub_mul,
    Matrix.smul_mul, one_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    ← Matrix.mul_assoc, trace_AAB A B hA hB]
  ring

private theorem trace_AABB (A B : BondMatrix R) (hB : B.trace = 0) :
    (A * A * B * B).trace = -B.det * (A * A).trace := by
  simpa only [Matrix.mul_assoc] using trace_ABB (A * A) B hB

private theorem trace_ABAB (A B : BondMatrix R) :
    (A * B * A * B).trace = (A * B).trace ^ 2 - 2 * (A.det * B.det) := by
  rw [Matrix.mul_assoc (A * B) A B, trace_square, Matrix.det_mul]

private theorem trace_ABBB (A B : BondMatrix R) (hB : B.trace = 0) :
    (A * B * B * B).trace = -B.det * (A * B).trace := by
  exact trace_ABB (A * B) B hB

/-- The four positive-power traces of the literal mixed transfer give the
Newton power sums for the trace-aligned quartic. The trace conditions are
imposed on each independent binary core. -/
theorem mixedTransfer_trace_powers (ket bra : Fin 2 → Matrix (Fin 2) (Fin 2) R) (k : R)
    (hket0 : (ket 0).trace = 1) (hket1 : (ket 1).trace = 0)
    (hbra0 : (bra 0).trace = 1) (hbra1 : (bra 1).trace = 0)
    (hket01 : (ket 0 * ket 1).trace = k) (hbra01 : (bra 0 * bra 1).trace = k) :
    let d := (ket 0).det
    let db := (bra 0).det
    let e := (ket 1).det
    let eb := (bra 1).det
    let U := d * db
    let a := d + db - 2 * (U + e * eb) - k ^ 2
    let b := U - e * eb
    let c := b ^ 2 + k ^ 2 * (d + eb) * (db + e)
    let T := (bra 0 ⊗ₖ ket 0) + (bra 1 ⊗ₖ ket 1)
    T.trace = 1 ∧ (T ^ 2).trace = 1 - 2 * a ∧
      (T ^ 3).trace = 1 - 3 * a + 3 * b ∧
      (T ^ 4).trace = 1 - 4 * a + 2 * a ^ 2 + 4 * b - 4 * c := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.trace_add, Matrix.trace_kronecker,
      hket0, hket1, hbra0, hbra1]
  · rw [trace_add_sq]
    simp only [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, trace_square,
      hket0, hket1, hbra0, hbra1, hket01, hbra01]
    ring
  · rw [trace_add_cube]
    simp only [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, trace_cube,
      trace_AAB _ _ hbra0 hbra1, trace_AAB _ _ hket0 hket1,
      trace_ABB _ _ hbra1, trace_ABB _ _ hket1,
      hket0, hket1, hbra0, hbra1, hket01, hbra01]
    ring
  · rw [trace_add_fourth]
    simp only [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, trace_fourth,
      trace_AAAB _ _ hbra0 hbra1, trace_AAAB _ _ hket0 hket1,
      trace_AABB _ _ hbra1, trace_AABB _ _ hket1, trace_ABAB,
      trace_ABBB _ _ hbra1, trace_ABBB _ _ hket1, trace_square,
      hket0, hket1, hbra0, hbra1, hket01, hbra01]
    ring

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTransferTracePowers
