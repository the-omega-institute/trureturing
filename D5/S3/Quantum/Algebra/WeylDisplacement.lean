/- GID: D5/S3/Quantum/Algebra/WeylDisplacement
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylDisplacement
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Weyl displacement words compose with a cocycle phase over a finite cyclic window. -/

/- Library-search audit trail (2026-09-01). Every line below is a search that was run,
   with the instrument, the query, and the count it returned.

   * Pinned mathlib in this worktree, 8688 `.lean` files. `Heisenberg`, `generalized Pauli`,
     `clockMatrix`, `shiftMatrix`, and `displacement operator` each return zero files.
     `Weyl` returns fourteen files; all fourteen were opened and every one is the Weyl group
     of a root system, an affine Weyl group, a Weyl chamber or character, or the convex-cone
     `Weyl theorem`. None is Weyl-Heisenberg.
   * Pinned Batteries in this worktree, 256 `.lean` files. All seven queries return zero.
   * `leanprover/cslib` by GitHub code search. `Weyl`, `Pauli`, `Heisenberg`, `clockMatrix`,
     and `shiftMatrix` return zero. The one `displacement` hit is a Turing-machine tape lemma.
   * `TauCetiProject/TauCeti` by GitHub code search. `clockMatrix`, `shiftMatrix`, and `Pauli`
     return zero. `Weyl` returns ten files, all opened, all root-system or Lie-theoretic Weyl
     groups. None is Weyl-Heisenberg.
   * Open mathlib pull requests by GitHub search: `Weyl-Heisenberg`, `generalized Pauli`,
     `clock shift matrix`, and `displacement operator` each return zero open pull requests.
   * Zulip was searched only through a web index of the public archive, which surfaced no topic
     proposing or claiming this formalization. That instrument is weaker than the code searches
     above and the archive's own search was not queried directly, so this domain is recorded as
     a weaker negative rather than an exhaustive one.
   * Outside the search domain but adjacent, and recorded so the reader can judge overlap:
     `inQWIRE/LeanQuantum` carries `structure Pauli (n : Nat)` with an `(-i)^m` phase, which is
     the symplectic presentation of the n-qubit Pauli group. That is the two-dimensional case
     tensored, not the clock and shift pair at general dimension formalized here.

   * The clock and shift generators, their Weyl relation, their orders, and their unitarity are
     already frozen in `D5/S3/Observer/WindowRegister`; this module imports them and reproves
     none of them. What is absent everywhere searched is the displacement word `X ^ a * Z ^ b`
     and the phase it acquires under composition, which is what this module supplies.
   * The finite Weyl-Heisenberg group these words generate is classical, so no novelty is
     claimed. See `Library/Quantum/appleby2005symmetric.md` for the background reference and for
     the exact limits of what was verified about it.
-/

import D5.S3.Observer.WindowRegister

/-!
# Weyl displacement words over a finite cyclic window

`displacement M a b` is the word `X ^ a * Z ^ b` in the frozen window generators.
Composing two such words returns a third, multiplied by a phase that depends only on
the clock exponent of the left factor and the shift exponent of the right one. The
squaring identity is the diagonal case of that composition law.
-/

namespace D5.S3.Quantum.Algebra.WeylDisplacement

open D5.S3.Observer.WindowRegister

noncomputable section

variable {M : ℕ} [NeZero M]

/-- The window phase only sees its exponent modulo the window cardinality. -/
private theorem windowRoot_pow_mod (n : ℕ) :
    windowRoot M ^ (n % M) = windowRoot M ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n M]
  rw [pow_add, pow_mul, (windowRoot_isPrimitiveRoot M).pow_eq_one, one_pow, one_mul]

/-- The cyclic update only sees its exponent modulo the window cardinality. -/
private theorem shiftMatrix_pow_mod (n : ℕ) :
    shiftMatrix M ^ (n % M) = shiftMatrix M ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n M]
  rw [pow_add, pow_mul, shiftMatrix_pow_card, one_pow, one_mul]

/-- The clock only sees its exponent modulo the window cardinality. -/
private theorem clockMatrix_pow_mod (n : ℕ) :
    clockMatrix M ^ (n % M) = clockMatrix M ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n M]
  rw [pow_add, pow_mul, clockMatrix_pow_card, one_pow, one_mul]

/-- Moving the clock across a shift power multiplies by that many window phases. -/
private theorem clockMatrix_mul_shiftMatrix_pow (n : ℕ) :
    clockMatrix M * shiftMatrix M ^ n =
      windowRoot M ^ n • (shiftMatrix M ^ n * clockMatrix M) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        clockMatrix M * shiftMatrix M ^ (n + 1)
            = clockMatrix M * shiftMatrix M ^ n * shiftMatrix M := by
              rw [pow_succ, mul_assoc]
        _ = (windowRoot M ^ n • (shiftMatrix M ^ n * clockMatrix M)) * shiftMatrix M := by
              rw [ih]
        _ = windowRoot M ^ n • (shiftMatrix M ^ n * (clockMatrix M * shiftMatrix M)) := by
              rw [Matrix.smul_mul, mul_assoc]
        _ = windowRoot M ^ n •
              (shiftMatrix M ^ n * (windowRoot M • (shiftMatrix M * clockMatrix M))) := by
              rw [window_weyl]
        _ = (windowRoot M ^ n * windowRoot M) •
              (shiftMatrix M ^ n * shiftMatrix M * clockMatrix M) := by
              rw [Matrix.mul_smul, smul_smul, mul_assoc]
        _ = windowRoot M ^ (n + 1) • (shiftMatrix M ^ (n + 1) * clockMatrix M) := by
              rw [← pow_succ, ← pow_succ]

/-- Moving a clock power across a shift power multiplies by the product of the exponents. -/
private theorem clockMatrix_pow_mul_shiftMatrix_pow (m n : ℕ) :
    clockMatrix M ^ m * shiftMatrix M ^ n =
      windowRoot M ^ (m * n) • (shiftMatrix M ^ n * clockMatrix M ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        clockMatrix M ^ (m + 1) * shiftMatrix M ^ n
            = clockMatrix M ^ m * (clockMatrix M * shiftMatrix M ^ n) := by
              rw [pow_succ, mul_assoc]
        _ = clockMatrix M ^ m * (windowRoot M ^ n • (shiftMatrix M ^ n * clockMatrix M)) := by
              rw [clockMatrix_mul_shiftMatrix_pow]
        _ = windowRoot M ^ n • (clockMatrix M ^ m * shiftMatrix M ^ n * clockMatrix M) := by
              rw [Matrix.mul_smul, mul_assoc]
        _ = windowRoot M ^ n •
              ((windowRoot M ^ (m * n) • (shiftMatrix M ^ n * clockMatrix M ^ m)) *
                clockMatrix M) := by
              rw [ih]
        _ = (windowRoot M ^ n * windowRoot M ^ (m * n)) •
              (shiftMatrix M ^ n * (clockMatrix M ^ m * clockMatrix M)) := by
              rw [Matrix.smul_mul, smul_smul, mul_assoc]
        _ = windowRoot M ^ ((m + 1) * n) • (shiftMatrix M ^ n * clockMatrix M ^ (m + 1)) := by
              rw [← pow_add, ← pow_succ]
              ring_nf

/-- The Weyl displacement word `D (a, b) = X ^ a * Z ^ b` in the window generators. -/
noncomputable def displacement (M : ℕ) [NeZero M] (a b : ZMod M) :
    Matrix (ZMod M) (ZMod M) ℂ :=
  shiftMatrix M ^ a.val * clockMatrix M ^ b.val

/-- The displacement word at the zero index is the identity. -/
@[simp] theorem displacement_zero : displacement M (0 : ZMod M) (0 : ZMod M) = 1 := by
  simp [displacement]

/-- Composition law: the phase is the clock exponent of the left factor times the
shift exponent of the right factor. -/
theorem displacement_mul (a b c d : ZMod M) :
    displacement M a b * displacement M c d =
      windowRoot M ^ (b * c).val • displacement M (a + c) (b + d) := by
  have hshift : shiftMatrix M ^ (a + c).val = shiftMatrix M ^ a.val * shiftMatrix M ^ c.val := by
    rw [ZMod.val_add, shiftMatrix_pow_mod, pow_add]
  have hclock : clockMatrix M ^ (b + d).val = clockMatrix M ^ b.val * clockMatrix M ^ d.val := by
    rw [ZMod.val_add, clockMatrix_pow_mod, pow_add]
  have hphase : windowRoot M ^ (b * c).val = windowRoot M ^ (b.val * c.val) := by
    rw [ZMod.val_mul, windowRoot_pow_mod]
  calc
    displacement M a b * displacement M c d
        = shiftMatrix M ^ a.val *
            (clockMatrix M ^ b.val * shiftMatrix M ^ c.val) * clockMatrix M ^ d.val := by
          simp only [displacement, mul_assoc]
    _ = shiftMatrix M ^ a.val *
          (windowRoot M ^ (b.val * c.val) •
            (shiftMatrix M ^ c.val * clockMatrix M ^ b.val)) * clockMatrix M ^ d.val := by
          rw [clockMatrix_pow_mul_shiftMatrix_pow]
    _ = windowRoot M ^ (b * c).val •
          (shiftMatrix M ^ a.val * shiftMatrix M ^ c.val *
            (clockMatrix M ^ b.val * clockMatrix M ^ d.val)) := by
          rw [hphase, Matrix.mul_smul, Matrix.smul_mul]
          congr 1
          simp only [mul_assoc]
    _ = windowRoot M ^ (b * c).val • displacement M (a + c) (b + d) := by
          rw [displacement, hshift, hclock]

/-- Squaring identity: `D p ^ 2 = w ^ (a * b) * D (2 p)`, the diagonal composition case. -/
theorem displacement_sq (a b : ZMod M) :
    displacement M a b ^ 2 =
      windowRoot M ^ (a * b).val • displacement M (a + a) (b + b) := by
  rw [pow_two, displacement_mul, mul_comm b a]

/-- Two displacement words commute after the symplectic phases are applied on both sides. -/
theorem displacement_comm (a b c d : ZMod M) :
    windowRoot M ^ (d * a).val • (displacement M a b * displacement M c d) =
      windowRoot M ^ (b * c).val • (displacement M c d * displacement M a b) := by
  rw [displacement_mul, displacement_mul, smul_smul, smul_smul, add_comm c a, add_comm d b,
    mul_comm (windowRoot M ^ (d * a).val)]

/-- The composition phase is a genuine sign, not a vacuous factor: on the two-address
window the words `D (0, 1)` and `D (1, 0)` anticommute. -/
theorem displacement_two_anticommute :
    displacement 2 (0 : ZMod 2) (1 : ZMod 2) * displacement 2 (1 : ZMod 2) (0 : ZMod 2) =
      -(displacement 2 (1 : ZMod 2) (0 : ZMod 2) *
          displacement 2 (0 : ZMod 2) (1 : ZMod 2)) := by
  have hroot : windowRoot 2 = -1 :=
    (windowRoot_isPrimitiveRoot 2).eq_neg_one_of_two_right
  rw [displacement_mul, displacement_mul]
  norm_num [hroot]
  rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one, neg_smul, one_smul]


/-- The composition phase is not a vacuous factor: on the two-address window the two
displacement words genuinely fail to commute. -/
theorem displacement_two_not_commute :
    displacement 2 (0 : ZMod 2) (1 : ZMod 2) * displacement 2 (1 : ZMod 2) (0 : ZMod 2) ≠
      displacement 2 (1 : ZMod 2) (0 : ZMod 2) *
        displacement 2 (0 : ZMod 2) (1 : ZMod 2) := by
  intro heq
  rw [displacement_mul, displacement_mul] at heq
  simp only [zero_add, add_zero] at heq
  have hval : ZMod.val (1 : ZMod 2) = 1 := rfl
  have hD : displacement 2 (1 : ZMod 2) (1 : ZMod 2) = shiftMatrix 2 * clockMatrix 2 := by
    simp [displacement, hval]
  have hentry : (shiftMatrix 2 * clockMatrix 2) (0 : ZMod 2) (1 : ZMod 2) = windowRoot 2 := by
    rw [clockMatrix, Matrix.mul_diagonal, shiftMatrix, Matrix.circulant_apply,
      if_pos (by decide), one_mul, ZMod.val_one'' (by norm_num : (2 : ℕ) ≠ 1), pow_one]
  have hcoord := congrFun (congrFun heq (0 : ZMod 2)) (1 : ZMod 2)
  rw [hD] at hcoord
  simp only [Matrix.smul_apply, smul_eq_mul, hentry] at hcoord
  norm_num [hval] at hcoord
  have hne : windowRoot 2 ≠ 0 := (windowRoot_isPrimitiveRoot 2).ne_zero (by norm_num)
  have hone : windowRoot 2 = 1 := by
    apply mul_left_cancel₀ hne
    simpa using hcoord
  exact (windowRoot_isPrimitiveRoot 2).ne_one (by norm_num) hone


end

end D5.S3.Quantum.Algebra.WeylDisplacement
