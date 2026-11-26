/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/PauliRows
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/PauliRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Each quaternion generator has fixed-point-free defect order 2^64. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Rank128Lattice
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The integral rows in the Barnes–Wall Gauss calculation are the coordinate
actions of the Pauli generators on the normalized tensor basis of
arXiv:2411.13646v2, Appendix A.1. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.PauliRows

open Q8TraceSign (Word integralRow)
open Rank128Lattice (B)
open Matrix

open private rowExponent rowFactor from
  D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Rank128Lattice

private def basisNumerator (u k : Word) : ℤ :=
  if k.val &&& u.val = k.val then 2 ^ rowExponent u else 0

private theorem B_eq_numerator (u k : Word) :
    B u k = (basisNumerator u k : ℚ) / 4 := by
  by_cases h : k.val &&& u.val = k.val
  · simp [B, basisNumerator, rowFactor, h, Int.cast_pow]
  · simp [B, basisNumerator, h]

private theorem row_sum_eq_numerator (row : List (Word × ℤ)) (k : Word) :
    (row.map fun e => (e.2 : ℚ) * B e.1 k).sum =
      (((row.map fun e => e.2 * basisNumerator e.1 k).sum : ℤ) : ℚ) / 4 := by
  induction row with
  | nil => simp
  | cons e row ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, add_div]
    rw [ih, B_eq_numerator, mul_div_assoc]

private def rowNumerator (mask : ℕ) (isSign : Bool) (u k : Word) : ℤ :=
  ((integralRow mask isSign u).map fun e => e.2 * basisNumerator e.1 k).sum

private def signExponent (mask : ℕ) (k : Word) : ℕ :=
  if k.val.testBit (if mask = 64 then 6 else 5) then 1 else 0

set_option maxHeartbeats 0 in
-- This check fixes one basis word and ranges over the ambient coordinates.
set_option maxRecDepth 4096 in
private theorem numerator_X_check : ∀ u k : Word,
    rowNumerator 64 false u k = basisNumerator u (Fin.ofNat 128 (k.val ^^^ 64)) ∧
    rowNumerator 32 false u k = basisNumerator u (Fin.ofNat 128 (k.val ^^^ 32)) := by
  intro u
  fin_cases u <;> decide +kernel

set_option maxHeartbeats 0 in
-- This check evaluates the two coordinate signs for each fixed basis word.
set_option maxRecDepth 4096 in
private theorem numerator_Z_check : ∀ u k : Word,
    rowNumerator 64 true u k = (-1 : ℤ) ^ signExponent 64 k * basisNumerator u k ∧
    rowNumerator 32 true u k = (-1 : ℤ) ^ signExponent 32 k * basisNumerator u k := by
  intro u
  fin_cases u <;> decide +kernel

/-- Pauli X on either selected tensor slot permutes the ambient coordinates
by xor with the mask. -/
theorem integralRow_X {mask : ℕ} (hmask : mask = 64 ∨ mask = 32) (u k : Word) :
    ((integralRow mask false u).map fun e => (e.2 : ℚ) * B e.1 k).sum =
      B u (Fin.ofNat 128 (k.val ^^^ mask)) := by
  have h : rowNumerator mask false u k = basisNumerator u (Fin.ofNat 128 (k.val ^^^ mask)) := by
    rcases hmask with rfl | rfl
    · exact (numerator_X_check u k).1
    · exact (numerator_X_check u k).2
  rw [row_sum_eq_numerator]
  change (rowNumerator mask false u k : ℚ) / 4 = _
  rw [h, B_eq_numerator]

/-- Pauli Z on either selected tensor slot multiplies each ambient coordinate
by the sign of its selected bit. -/
theorem integralRow_Z {mask : ℕ} (hmask : mask = 64 ∨ mask = 32) (u k : Word) :
    ((integralRow mask true u).map fun e => (e.2 : ℚ) * B e.1 k).sum =
      (-1 : ℚ) ^ (if k.val.testBit (if mask = 64 then 6 else 5) then (1 : ℕ) else 0) * B u k := by
  have h : rowNumerator mask true u k = (-1 : ℤ) ^ signExponent mask k * basisNumerator u k := by
    rcases hmask with rfl | rfl
    · exact (numerator_Z_check u k).1
    · exact (numerator_Z_check u k).2
  rw [row_sum_eq_numerator]
  change (rowNumerator mask true u k : ℚ) / 4 = (-1 : ℚ) ^ signExponent mask k * B u k
  simp only [h, B_eq_numerator, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    mul_div_assoc]

private def flip (mask : ℕ) (u : Word) : Word := Fin.ofNat 128 (u.val ^^^ mask)

private def bitSign (b : Bool) : ℚ := if b then -1 else 1

private def signRow (p : Word → Word) (s : Word → ℚ) : Matrix Word Word ℚ :=
  fun u v => if v = p u then s u else 0

private theorem signRow_mul (p q : Word → Word) (s t : Word → ℚ) :
    signRow p s * signRow q t = signRow (q ∘ p) (fun u => s u * t (p u)) := by
  ext u v
  rw [Matrix.mul_apply, Finset.sum_eq_single (p u)]
  · by_cases hv : v = q (p u) <;> simp [signRow, hv]
  · intro a _ ha
    simp [signRow, ha]
  · intro h
    exact (h (Finset.mem_univ _)).elim

private def X (mask : ℕ) : Matrix Word Word ℚ := signRow (flip mask) (fun _ => 1)
private def Z (slot : ℕ) : Matrix Word Word ℚ :=
  signRow id (fun u => bitSign (u.val.testBit slot))

/-- The quaternion generators and their product in ambient coordinates,
using the row-action order of the lattice lift. -/
def generatorMatrix : Fin 3 → Matrix Word Word ℚ
  | 0 => X 64 * Z 6
  | 1 => (X 64 * X 32) * Z 5
  | 2 => (X 64 * Z 6) * ((X 64 * X 32) * Z 5)

private def direction (r : Fin 3) : Word → Word :=
  match r with
  | 0 => flip 64
  | 1 => flip 96
  | 2 => flip 32

private def phase (r : Fin 3) (u : Word) : ℚ :=
  match r with
  | 0 => bitSign (!(u.val.testBit 6))
  | 1 => bitSign (!(u.val.testBit 5))
  | 2 => bitSign (xor (u.val.testBit 6) (u.val.testBit 5))

private theorem i_words : ∀ u : Word,
    (id ∘ flip 64) u = direction 0 u ∧
      (1 : ℚ) * bitSign ((flip 64 u).val.testBit 6) = phase 0 u := by decide +kernel

private theorem j_words : ∀ u : Word,
    (id ∘ (flip 32 ∘ flip 64)) u = direction 1 u ∧
      ((1 : ℚ) * 1) * bitSign ((flip 32 (flip 64 u)).val.testBit 5) = phase 1 u := by
  decide +kernel

private theorem k_words : ∀ u : Word,
    direction 1 (direction 0 u) = direction 2 u ∧
      phase 0 u * phase 1 (direction 0 u) = phase 2 u := by decide +kernel

private theorem i_matrix : generatorMatrix 0 = signRow (direction 0) (phase 0) := by
  change X 64 * Z 6 = _
  rw [X, Z, signRow_mul, show id ∘ flip 64 = direction 0 from funext fun u => (i_words u).1,
    show (fun u => (1 : ℚ) * bitSign ((flip 64 u).val.testBit 6)) = phase 0 from
      funext fun u => (i_words u).2]

private theorem j_matrix : generatorMatrix 1 = signRow (direction 1) (phase 1) := by
  change (X 64 * X 32) * Z 5 = _
  simp only [X, Z, signRow_mul, Function.comp_apply]
  rw [show id ∘ (flip 32 ∘ flip 64) = direction 1 from funext fun u => (j_words u).1,
    show (fun u => ((1 : ℚ) * 1) * bitSign ((flip 32 (flip 64 u)).val.testBit 5)) =
      phase 1 from funext fun u => (j_words u).2]

private theorem generator_rows (r : Fin 3) :
    generatorMatrix r = signRow (direction r) (phase r) := by
  fin_cases r
  · exact i_matrix
  · exact j_matrix
  · change generatorMatrix 0 * generatorMatrix 1 = _
    rw [i_matrix, j_matrix, signRow_mul,
      show direction 1 ∘ direction 0 = direction 2 from funext fun u => (k_words u).1,
      show (fun u => phase 0 u * phase 1 (direction 0 u)) = phase 2 from
        funext fun u => (k_words u).2]
    rfl

private theorem quaternion_rows : ∀ r : Fin 3, ∀ u : Word,
    direction r (direction r u) = u ∧ phase r (direction r u) = -phase r u ∧
      phase r u * phase r (direction r u) = -1 := by decide +kernel

/-- The ambient Pauli words are fixed-point-free quarter turns. -/
theorem generator_square (r : Fin 3) : generatorMatrix r * generatorMatrix r = -1 := by
  rw [generator_rows, signRow_mul]
  ext u v
  have h := quaternion_rows r u
  by_cases hv : v = u
  · subst v
    simp [signRow, h.1, h.2.2]
  · simp [signRow, Function.comp_apply, h.1, hv, Ne.symm hv]

private theorem generator_transpose (r : Fin 3) : (generatorMatrix r)ᵀ = -generatorMatrix r := by
  rw [generator_rows]
  ext u v
  change (if u = direction r v then phase r v else 0) =
    -(if v = direction r u then phase r u else 0)
  by_cases h : v = direction r u
  · subst v
    simp [(quaternion_rows r u).1, (quaternion_rows r u).2.1]
  · have hn : u ≠ direction r v := by
      intro hu
      apply h
      rw [hu, (quaternion_rows r v).1]
    simp [h, hn]

/-- The fixed-point-free defect has order 2^64 for each generator. -/
theorem defect_abs_det (r : Fin 3) : |(1 - generatorMatrix r).det| = (2 : ℚ) ^ 64 := by
  let A := generatorMatrix r
  have hprod : (1 - A) * (1 - A)ᵀ = (2 : ℚ) • (1 : Matrix Word Word ℚ) := by
    dsimp only [A]
    rw [Matrix.transpose_sub, Matrix.transpose_one, generator_transpose r, sub_neg_eq_add,
      sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, generator_square r]
    rw [two_smul]
    abel
  have hd := congrArg Matrix.det hprod
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin] at hd
  have hp : |(1 - A).det| ^ 2 = ((2 : ℚ) ^ 64) ^ 2 := by
    rw [sq_abs, pow_two ((1 - A).det), hd, ← pow_mul]
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) (by decide)).mp hp

#print axioms defect_abs_det
#print axioms integralRow_X
#print axioms integralRow_Z

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.PauliRows
