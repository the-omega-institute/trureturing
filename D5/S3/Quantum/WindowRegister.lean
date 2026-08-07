/- GID: D5/S3/Quantum/WindowRegister
   generality: G
   mirror-B: D5/B/S3/Quantum/WindowRegister
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove finite cyclic window Weyl relations and scalar commutant rigidity. -/

import D5.S3.Fourier.FinitePoisson
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace D5.S3.Quantum.WindowRegister

open D5.S3.Fourier.FinitePoisson

noncomputable section

variable {M : ℕ} [NeZero M]

/-- The positive standard primitive `M`-th root used by a cyclic window. -/
noncomputable def windowRoot (M : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / M)

/-- The window phase is a primitive root of the full window cardinality. -/
theorem windowRoot_isPrimitiveRoot (M : ℕ) [NeZero M] :
    IsPrimitiveRoot (windowRoot M) M := by
  simpa [windowRoot] using Complex.isPrimitiveRoot_exp M (NeZero.ne M)

/-- The address-reading clock in the standard cyclic basis. -/
noncomputable def clockMatrix (M : ℕ) : Matrix (ZMod M) (ZMod M) ℂ :=
  Matrix.diagonal (fun i => windowRoot M ^ i.val)

/-- The one-address cyclic update. `circulant` uses the convention `v (i - j)`. -/
def shiftMatrix (M : ℕ) [NeZero M] : Matrix (ZMod M) (ZMod M) ℂ :=
  Matrix.circulant (fun i => if i = 1 then 1 else 0)

private theorem windowRoot_eq_character_one :
    windowRoot M = character (m := M) 1 1 := by
  rw [character_apply, one_mul]
  simpa [windowRoot] using (ZMod.stdAddChar_coe (N := M) (1 : ℤ)).symm

private theorem windowRoot_pow_val_eq_character (i : ZMod M) :
    windowRoot M ^ i.val = character (m := M) 1 i := by
  rw [windowRoot_eq_character_one, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [i.natCast_zmod_val]

private def shiftPerm (M : ℕ) : Equiv.Perm (ZMod M) :=
  Equiv.subRight 1

private theorem shiftMatrix_eq_permMatrix :
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
private theorem shiftPerm_pow_apply (n : ℕ) (i : ZMod M) :
    (shiftPerm M ^ n) i = i - (n : ZMod M) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp only [shiftPerm, Equiv.subRight_apply, Nat.cast_succ]
      ring

/- Provenance: `OBSERVER-QUANTUM.md` section 3, restricted to the fixed finite matrix window. -/
/-- The clock and cyclic shift obey the finite Weyl relation. -/
theorem window_weyl (M : ℕ) [NeZero M] :
    clockMatrix M * shiftMatrix M = windowRoot M • (shiftMatrix M * clockMatrix M) := by
  ext i j
  simp only [clockMatrix, shiftMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.circulant_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : i - j = 1
  · rw [if_pos h, one_mul, mul_one]
    have hij : i = j + 1 := by
      rw [sub_eq_iff_eq_add] at h
      simpa [add_comm] using h
    subst i
    rw [windowRoot_pow_val_eq_character, windowRoot_pow_val_eq_character,
      windowRoot_eq_character_one]
    simpa [mul_comm] using
      (AddChar.map_add_eq_mul (character (m := M) 1) j 1)
  · simp [h]

/-- The cyclic update returns after exactly the window-cardinality power.
This is the fixed-window relation only; it does not assert a central winding phase. -/
theorem shiftMatrix_pow_card : shiftMatrix M ^ M = 1 := by
  rw [shiftMatrix_eq_permMatrix]
  have hPerm : shiftPerm M ^ M = 1 := by
    ext i
    rw [shiftPerm_pow_apply]
    simp
  have hInvPerm : (shiftPerm M)⁻¹ ^ M = 1 := by
    rw [inv_pow, hPerm, inv_one]
  have hMap := congrArg (Matrix.permMatrixHom (n := ZMod M) (R := ℂ)) hInvPerm
  rw [map_pow, map_one] at hMap
  change (((shiftPerm M)⁻¹)⁻¹).permMatrix ℂ ^ M = 1 at hMap
  simpa only [inv_inv] using hMap

/-- The clock phases return after the window-cardinality power. -/
theorem clockMatrix_pow_card : clockMatrix M ^ M = 1 := by
  rw [clockMatrix, Matrix.diagonal_pow, Matrix.diagonal_eq_one]
  funext i
  simp only [Pi.pow_apply, ← pow_mul]
  rw [mul_comm, pow_mul, (windowRoot_isPrimitiveRoot M).pow_eq_one, one_pow]
  simp

/-- Both finite-window generators are unitary. -/
theorem window_unitary :
    star (shiftMatrix M) * shiftMatrix M = 1 ∧
      star (clockMatrix M) * clockMatrix M = 1 := by
  constructor
  · rw [shiftMatrix_eq_permMatrix, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix]
    simpa using
      (Matrix.permMatrix_mul (R := ℂ) (shiftPerm M) (shiftPerm M)⁻¹).symm
  · rw [clockMatrix, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    have hNorm : ‖windowRoot M ^ i.val‖ = 1 := by
      rw [norm_pow, (windowRoot_isPrimitiveRoot M).norm'_eq_one (NeZero.ne M), one_pow]
    simpa [RCLike.star_def, hNorm] using
      (RCLike.conj_mul (windowRoot M ^ i.val))

/- Provenance: `OBSERVER-QUANTUM.md` section 3, after fixing the winding account. -/
/-- A matrix commuting with both finite-window generators is a scalar matrix. -/
theorem window_commutant_eq_scalars (A : Matrix (ZMod M) (ZMod M) ℂ)
    (hC : Commute A (clockMatrix M)) (hS : Commute A (shiftMatrix M)) :
    A ∈ Set.range (Matrix.scalar (ZMod M)) := by
  have hClockEntry (i j : ZMod M) :
      A i j * windowRoot M ^ j.val = windowRoot M ^ i.val * A i j := by
    have h := congr($(hC.eq) i j)
    simpa [clockMatrix] using h
  have hPhaseNe (i j : ZMod M) (hij : i ≠ j) :
      windowRoot M ^ i.val ≠ windowRoot M ^ j.val := by
    intro h
    have hval : i.val = j.val :=
      (windowRoot_isPrimitiveRoot M).pow_inj i.val_lt j.val_lt h
    exact hij (ZMod.val_injective M hval)
  have hOffDiag (i j : ZMod M) (hij : i ≠ j) : A i j = 0 := by
    have hProduct :
        (windowRoot M ^ j.val - windowRoot M ^ i.val) * A i j = 0 := by
      calc
        (windowRoot M ^ j.val - windowRoot M ^ i.val) * A i j =
            A i j * windowRoot M ^ j.val - windowRoot M ^ i.val * A i j := by ring
        _ = 0 := sub_eq_zero.mpr (hClockEntry i j)
    exact (mul_eq_zero.mp hProduct).resolve_left
      (sub_ne_zero.mpr (hPhaseNe i j hij).symm)
  have hShift :
      A * (shiftPerm M).permMatrix ℂ = (shiftPerm M).permMatrix ℂ * A := by
    simpa only [← shiftMatrix_eq_permMatrix] using hS.eq
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul] at hShift
  have hDiagStep (i : ZMod M) : A i i = A (i - 1) (i - 1) := by
    have h := congr($(hShift) i (i - 1))
    simpa [shiftPerm, Matrix.submatrix_apply] using h
  have hDiagIter (i : ZMod M) (n : ℕ) :
      A i i = A (i - (n : ZMod M)) (i - (n : ZMod M)) := by
    induction n generalizing i with
    | zero => simp
    | succ n ih =>
        calc
          A i i = A (i - 1) (i - 1) := hDiagStep i
          _ = A ((i - 1) - (n : ZMod M)) ((i - 1) - (n : ZMod M)) := ih (i - 1)
          _ = A (i - (n + 1 : ℕ)) (i - (n + 1 : ℕ)) := by
            push_cast
            ring_nf
  have hDiag (i : ZMod M) : A i i = A 0 0 := by
    have h := hDiagIter i i.val
    simpa [i.natCast_zmod_val] using h
  refine ⟨A 0 0, ?_⟩
  ext i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp [hDiag]
  · simp [hij, hOffDiag i j hij]

end

end D5.S3.Quantum.WindowRegister
