/- GID: D5/S3/Observer/WindowRegisterCRT
   generality: G
   mirror-B: D5/B/S3/Observer/WindowRegisterCRT
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose a coprime finite window pair into two exact CRT tensor factors. -/

/- Library-search audit trail (2026-08-10):
   * `ZMod.chineseRemainder` supplies the canonical ring equivalence from
     `ZMod (m * n)` to `ZMod m x ZMod n` for coprime factors.
   * `Matrix.reindex` transports both matrix indices along that equivalence.
   * `Matrix.kronecker_apply` identifies the entries of the tensor factors.
   * No theorem combining these APIs with the window clock and shift matrices
     was found in the repository or the pinned Mathlib tree.
-/

import D5.S3.Observer.WindowRegister
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace D5.S3.Observer.WindowRegisterCRT

open D5.S3.Fourier.FinitePoisson
open D5.S3.Observer.WindowRegister
open scoped Kronecker

noncomputable section

variable {m n : ℕ} [NeZero m] [NeZero n]

private theorem window_root_eq_character_one (M : ℕ) [NeZero M] :
    windowRoot M = character (m := M) 1 1 := by
  rw [character_apply, one_mul]
  simpa [windowRoot] using (ZMod.stdAddChar_coe (N := M) (1 : ℤ)).symm

private theorem window_root_pow_val_eq_character
    (M : ℕ) [NeZero M] (i : ZMod M) :
    windowRoot M ^ i.val = character (m := M) 1 i := by
  rw [window_root_eq_character_one, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp [i.natCast_zmod_val]

private theorem window_root_pow_add
    (M : ℕ) [NeZero M] (i j : ZMod M) :
    windowRoot M ^ (i + j).val =
      windowRoot M ^ i.val * windowRoot M ^ j.val := by
  rw [window_root_pow_val_eq_character, window_root_pow_val_eq_character,
    window_root_pow_val_eq_character]
  exact AddChar.map_add_eq_mul (character (m := M) 1) i j

/-- The left CRT clock factor, obtained by restricting the global window phase
to the `ZMod m x {0}` summand. -/
noncomputable def crtLeftClockMatrix (h : Nat.Coprime m n) :
    Matrix (ZMod m) (ZMod m) ℂ :=
  Matrix.diagonal fun i =>
    windowRoot (m * n) ^ ((ZMod.chineseRemainder h).symm (i, 0)).val

/-- The right CRT clock factor, obtained by restricting the global window phase
to the `{0} x ZMod n` summand. -/
noncomputable def crtRightClockMatrix (h : Nat.Coprime m n) :
    Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.diagonal fun i =>
    windowRoot (m * n) ^ ((ZMod.chineseRemainder h).symm (0, i)).val

/-- Under the canonical CRT reindexing, the window clock and shift are exactly
the Kronecker products of their two coprime factors. This is the binary step;
no iterated prime-power tower is asserted here. -/
theorem window_register_crt_decomposition (h : Nat.Coprime m n) :
    Matrix.reindex (ZMod.chineseRemainder h).toEquiv
        (ZMod.chineseRemainder h).toEquiv (clockMatrix (m * n)) =
      crtLeftClockMatrix h ⊗ₖ crtRightClockMatrix h ∧
    Matrix.reindex (ZMod.chineseRemainder h).toEquiv
        (ZMod.chineseRemainder h).toEquiv (shiftMatrix (m * n)) =
      shiftMatrix m ⊗ₖ shiftMatrix n := by
  constructor
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, clockMatrix,
      Matrix.kronecker_apply, crtLeftClockMatrix, crtRightClockMatrix]
    by_cases h₁ : i₁ = j₁
    · subst j₁
      by_cases h₂ : i₂ = j₂
      · subst j₂
        simp only [Matrix.diagonal_apply_eq]
        have hsplit :
            (ZMod.chineseRemainder h).symm (i₁, i₂) =
              (ZMod.chineseRemainder h).symm (i₁, 0) +
                (ZMod.chineseRemainder h).symm (0, i₂) := by
          rw [← map_add]
          simp
        calc
          windowRoot (m * n) ^ ((ZMod.chineseRemainder h).symm (i₁, i₂)).val =
              windowRoot (m * n) ^
                ((ZMod.chineseRemainder h).symm (i₁, 0) +
                  (ZMod.chineseRemainder h).symm (0, i₂)).val := by
                    rw [hsplit]
          _ = _ := window_root_pow_add (m * n) _ _
      · have hpair : (i₁, i₂) ≠ (i₁, j₂) := by
          intro hp
          exact h₂ (congrArg Prod.snd hp)
        have hglobal :
            (ZMod.chineseRemainder h).symm (i₁, i₂) ≠
              (ZMod.chineseRemainder h).symm (i₁, j₂) :=
          (ZMod.chineseRemainder h).symm.injective.ne hpair
        simp [h₂, hglobal]
    · have hpair : (i₁, i₂) ≠ (j₁, j₂) := by
        intro hp
        exact h₁ (congrArg Prod.fst hp)
      have hglobal :
          (ZMod.chineseRemainder h).symm (i₁, i₂) ≠
            (ZMod.chineseRemainder h).symm (j₁, j₂) :=
        (ZMod.chineseRemainder h).symm.injective.ne hpair
      simp [h₁, hglobal]
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, shiftMatrix,
      Matrix.circulant_apply, Matrix.kronecker_apply]
    have hiff :
        (ZMod.chineseRemainder h).symm (i₁, i₂) -
            (ZMod.chineseRemainder h).symm (j₁, j₂) = 1 ↔
          i₁ - j₁ = 1 ∧ i₂ - j₂ = 1 := by
      constructor
      · intro hij
        have mapped := congrArg (ZMod.chineseRemainder h) hij
        simpa [Prod.ext_iff] using mapped
      · rintro ⟨hm, hn⟩
        have hp : (i₁, i₂) - (j₁, j₂) = 1 := Prod.ext hm hn
        calc
          (ZMod.chineseRemainder h).symm (i₁, i₂) -
              (ZMod.chineseRemainder h).symm (j₁, j₂) =
              (ZMod.chineseRemainder h).symm ((i₁, i₂) - (j₁, j₂)) := by
                rw [map_sub]
          _ = (ZMod.chineseRemainder h).symm 1 := congrArg _ hp
          _ = 1 := map_one _
    split_ifs with hg hm hn <;> simp_all

end

end D5.S3.Observer.WindowRegisterCRT
