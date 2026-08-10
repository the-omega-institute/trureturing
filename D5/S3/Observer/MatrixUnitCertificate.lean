/- GID: D5/S3/Observer/MatrixUnitCertificate
   generality: G
   mirror-B: D5/B/S3/Observer/MatrixUnitCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct exact matrix units from every finite cyclic window Weyl pair. -/

/- Library-search audit trail (2026-08-10):
   * `D5.S3.Fourier.FinitePoisson.characterEquiv` identifies the standard ZMod
     characters with the full character group.
   * `AddChar.sum_apply_eq_ite` supplies the exact finite character orthogonality.
   * `Matrix.single_mul_single_same`, `Matrix.single_mul_single_of_ne`, and
     `Matrix.sum_single_one` supply the standard matrix-unit algebra after the
     Fourier construction is identified entrywise.
-/

import D5.S3.Observer.WindowRegister

namespace D5.S3.Observer.MatrixUnitCertificate

open D5.S3.Fourier.FinitePoisson
open D5.S3.Observer.WindowRegister

noncomputable section

variable {M : ℕ} [NeZero M]

private def shiftPerm (M : ℕ) : Equiv.Perm (ZMod M) :=
  Equiv.subRight 1

private theorem shift_matrix_eq_perm_matrix :
    shiftMatrix M = (shiftPerm M).permMatrix ℂ := by
  ext i j
  simp only [shiftMatrix, Matrix.circulant_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]
  congr 1
  apply propext
  simp only [Option.some.injEq]
  constructor
  · intro h
    rw [sub_eq_iff_eq_add] at h
    rw [shiftPerm, Equiv.subRight_apply]
    linear_combination h
  · intro h
    rw [shiftPerm, Equiv.subRight_apply] at h
    linear_combination h

omit [NeZero M] in
private theorem shift_perm_pow_apply (n : ℕ) (i : ZMod M) :
    (shiftPerm M ^ n) i = i - (n : ZMod M) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp only [shiftPerm, Equiv.subRight_apply, Nat.cast_succ]
      ring

private theorem shift_matrix_pow_apply (n : ℕ) (r s : ZMod M) :
    (shiftMatrix M ^ n) r s =
      if r - s = (n : ZMod M) then 1 else 0 := by
  have hPower : shiftMatrix M ^ n = (shiftPerm M ^ n).permMatrix ℂ := by
    rw [shift_matrix_eq_perm_matrix]
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ih, ← Matrix.permMatrix_mul, pow_succ']
  rw [hPower]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, shift_perm_pow_apply]
  congr 1
  apply propext
  simp only [Option.some.injEq]
  constructor <;> intro h <;> linear_combination h

private theorem window_root_eq_character_one :
    windowRoot M = character (m := M) 1 1 := by
  rw [character_apply, one_mul]
  simpa [windowRoot] using (ZMod.stdAddChar_coe (N := M) (1 : ℤ)).symm

private theorem window_root_pow_val_eq_character (r : ZMod M) :
    windowRoot M ^ r.val = character (m := M) 1 r := by
  rw [window_root_eq_character_one, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [r.natCast_zmod_val]

private theorem clock_phase_pow_eq_character (r k : ZMod M) :
    (windowRoot M ^ r.val) ^ k.val = character (m := M) k r := by
  rw [window_root_pow_val_eq_character, ← AddChar.map_nsmul_eq_pow,
    nsmul_eq_mul, k.natCast_zmod_val]
  simp [character_apply, mul_comm]

private theorem coefficient_mul_clock_phase (i r k : ZMod M) :
    character (m := M) (-i) k * character (m := M) k r =
      character (m := M) k (r - i) := by
  rw [character_apply, character_apply, character_apply,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem sum_character (x : ZMod M) :
    ∑ k : ZMod M, character (m := M) k x =
      if x = 0 then (M : ℂ) else 0 := by
  calc
    ∑ k : ZMod M, character (m := M) k x =
        ∑ ψ : AddChar (ZMod M) ℂ, ψ x := by
      apply Fintype.sum_equiv (characterEquiv (m := M))
      intro k
      simp
    _ = if x = 0 then (Fintype.card (ZMod M) : ℂ) else 0 :=
      AddChar.sum_apply_eq_ite x
    _ = if x = 0 then (M : ℂ) else 0 := by rw [ZMod.card]

private theorem matrix_sum_apply
    (f : ZMod M → Matrix (ZMod M) (ZMod M) ℂ) (r s : ZMod M) :
    (∑ k, f k) r s = ∑ k, f k r s := by
  simpa using (Matrix.sum_apply r s Finset.univ f)

/-- The matrix unit obtained by Fourier-projecting the frozen clock onto address `i`
and then applying the frozen cyclic shift from column `j` to row `i`. -/
noncomputable def matrixUnit (M : ℕ) [NeZero M] (i j : ZMod M) :
    Matrix (ZMod M) (ZMod M) ℂ :=
  ((M : ℂ)⁻¹ • ∑ k : ZMod M,
      character (m := M) (-i) k • clockMatrix M ^ k.val) *
    shiftMatrix M ^ (i - j).val

/-- The finite Fourier construction is exactly the standard single-entry matrix. -/
theorem matrix_unit_eq_single (i j : ZMod M) :
    matrixUnit M i j = Matrix.single i j 1 := by
  have hProjector :
      (M : ℂ)⁻¹ • ∑ k : ZMod M,
          character (m := M) (-i) k • clockMatrix M ^ k.val =
        Matrix.single i i 1 := by
    ext r s
    by_cases hrs : r = s
    · subst s
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [matrix_sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul, clockMatrix,
        Matrix.diagonal_pow, Pi.pow_apply,
        Matrix.diagonal_apply_eq]
      simp_rw [clock_phase_pow_eq_character, coefficient_mul_clock_phase]
      rw [sum_character]
      by_cases hri : r = i
      · subst r
        simp [Nat.cast_ne_zero.mpr (NeZero.ne M)]
      · rw [if_neg (sub_ne_zero.mpr hri),
          Matrix.single_apply_of_row_ne (Ne.symm hri)]
        simp
    · simp only [Matrix.smul_apply, smul_eq_mul]
      rw [matrix_sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul, clockMatrix,
        Matrix.diagonal_pow]
      have hSum :
          ∑ k : ZMod M, character (m := M) (-i) k *
              Matrix.diagonal ((fun x : ZMod M => windowRoot M ^ x.val) ^ k.val) r s = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        rw [Matrix.diagonal_apply_ne _ hrs, mul_zero]
      rw [hSum, mul_zero]
      have hSingle : ¬(i = r ∧ i = s) := by
        intro h
        exact hrs (h.1.symm.trans h.2)
      rw [Matrix.single_apply_of_ne i i 1 r s hSingle]
  rw [matrixUnit, hProjector]
  ext r s
  by_cases hri : r = i
  · subst r
    simp only [Matrix.single_mul_apply_same, one_mul,
      shift_matrix_pow_apply, Matrix.single_apply]
    rw [(i - j).natCast_zmod_val]
    simp only [true_and]
    congr 1
    apply propext
    constructor <;> intro h <;> linear_combination h
  · rw [Matrix.single_mul_apply_of_ne 1 i i r s hri]
    rw [Matrix.single_apply_of_row_ne (Ne.symm hri)]

/-- The Weyl-generated matrix units satisfy their multiplication law as an exact
matrix identity, with the off-matching branch equal to zero and no error term. -/
theorem matrix_unit_mul (i j k l : ZMod M) :
    matrixUnit M i j * matrixUnit M k l =
      (if j = k then (1 : ℂ) else 0) • matrixUnit M i l := by
  rw [matrix_unit_eq_single, matrix_unit_eq_single, matrix_unit_eq_single]
  by_cases hjk : j = k
  · subst k
    simp
  · rw [Matrix.single_mul_single_of_ne 1 i j k hjk 1]
    simp [hjk]

/-- The diagonal Weyl-generated matrix units resolve the identity exactly. -/
theorem matrix_units_sum_diagonal :
    ∑ i : ZMod M, matrixUnit M i i = 1 := by
  simp_rw [matrix_unit_eq_single]
  exact Matrix.sum_single_one

end

end D5.S3.Observer.MatrixUnitCertificate
