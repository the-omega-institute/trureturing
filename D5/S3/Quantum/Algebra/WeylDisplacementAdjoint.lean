/- GID: D5/S3/Quantum/Algebra/WeylDisplacementAdjoint
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylDisplacementAdjoint
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The adjoint of a displacement word is the negated word times the symplectic phase. -/

/- Library-search audit trail (2026-09-01). The commands below are reproduced literally as they
   were run, one per line, each followed by the count it returned. Paths are relative to this
   worktree.

   grep -ril "Weyl-Heisenberg"     .lake/packages/mathlib --include='*.lean' | wc -l   -> 0
   grep -ril "displacement operator" .lake/packages/mathlib --include='*.lean' | wc -l -> 0
   grep -ril "clock matrix"        .lake/packages/mathlib --include='*.lean' | wc -l   -> 0
   grep -ril "shift matrix"        .lake/packages/mathlib --include='*.lean' | wc -l   -> 0
   grep -ril "generalized Pauli"   .lake/packages/mathlib --include='*.lean' | wc -l   -> 0
   The same five commands with .lake/packages/batteries in place of mathlib -> 0 each.

   gh search prs --repo leanprover-community/mathlib4 --state open "Weyl-Heisenberg" --limit 20
   gh search prs --repo leanprover-community/mathlib4 --state open "generalized Pauli" --limit 20
   gh search prs --repo leanprover-community/mathlib4 --state open "clock matrix" --limit 20
   gh search prs --repo leanprover-community/mathlib4 --state open "shift matrix" --limit 20
   gh search prs --repo leanprover-community/mathlib4 --state open "displacement operator"
     --limit 20
   gh search prs --repo leanprover-community/mathlib4 --state open "Sylvester clock" --limit 20
   Each returned zero open pull requests. An earlier conjunctive query in the same form with
   "clock shift unitary" also returned zero, but that is a weak signal: the same command with
   "clock", "shift" and "unitary" separately returns 23, 30 and 30. The six queries above, not
   that one, are what this claim rests on.

   gh search code --repo leanprover/cslib "conjTranspose Pauli" --limit 5              -> 0
   gh search code --repo leanprover/cslib "displacement" --limit 5                     -> 1
     That one hit is Cslib/Computability/Machines/Turing/MultiTape/TapeLemmas.lean.
   gh search code --repo TauCetiProject/TauCeti "conjTranspose Pauli" --limit 5        -> 0
   gh search code --repo TauCetiProject/TauCeti "displacement" --limit 10              -> 10
     All ten were opened. Every one is geometric or analytic displacement: Hadamard
     factorization, cotangent maps, homotopy displacement, Lie weight strings. None is a
     Weyl-Heisenberg displacement operator.

   git grep -n -E "star \\(?(shiftMatrix|clockMatrix)" origin/dev -- '*.lean'
     Two hits, both inside window_unitary in the frozen window register. No adjoint of a
     displacement word exists here. The `displacement` hits under D5/S1/Deficit/Displacement/
     are the Beatty and golden-substitution family, unrelated to these operators.

   Zulip was searched through a web index of the public archive with the string
   `leanprover zulip archive formalize adjoint "displacement operator" OR "clock and shift" OR
   "Weyl-Heisenberg" Lean mathlib quantum`, which surfaced no topic on formalizing these
   operators or their adjoint. The archive's own search was not queried directly, so this domain
   is a weaker negative than the commands above and is recorded as such.

   Two normalizations appear in the literature. The symmetric one carries a half-integer phase
   and makes the adjoint equal the negated word outright; the unnormalized one used here,
   X ^ a * Z ^ b, carries the whole phase in the adjoint law below. They differ by exactly that
   prefactor, and the unnormalized convention is the one the source proposition uses.

   The unitarity of the generators is already frozen in `D5/S3/Observer/WindowRegister`, and the
   composition law in `D5/S3/Quantum/Algebra/WeylDisplacement`. This module imports both, reproves
   neither, and supplies the adjoint identity, which none of the commands above found anywhere.
-/

import D5.S3.Quantum.Algebra.WeylDisplacement

/-!
# The adjoint of a Weyl displacement word

Conjugate-transposing `D (a, b) = X ^ a * Z ^ b` reverses the order of the two factors and
inverts each index. Restoring the original order costs exactly one symplectic phase, so the
adjoint is the word at the negated index scaled by that phase.
-/

namespace D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement

noncomputable section

variable {M : ℕ} [NeZero M]

/-- Negating an index produces the inverse power of the cyclic update. -/
theorem shiftMatrix_pow_neg_mul (a : ZMod M) :
    shiftMatrix M ^ (-a).val * shiftMatrix M ^ a.val = 1 := by
  rw [← pow_add]
  have hzero : ((-a).val + a.val) % M = 0 := by
    have hval : ((-a) + a).val = ((-a).val + a.val) % M := ZMod.val_add _ _
    simpa using hval.symm
  conv_lhs => rw [← Nat.div_add_mod ((-a).val + a.val) M]
  rw [hzero, Nat.add_zero, pow_mul, shiftMatrix_pow_card, one_pow]

/-- Negating an index produces the inverse power of the clock. -/
theorem clockMatrix_pow_neg_mul (b : ZMod M) :
    clockMatrix M ^ (-b).val * clockMatrix M ^ b.val = 1 := by
  rw [← pow_add]
  have hzero : ((-b).val + b.val) % M = 0 := by
    have hval : ((-b) + b).val = ((-b).val + b.val) % M := ZMod.val_add _ _
    simpa using hval.symm
  conv_lhs => rw [← Nat.div_add_mod ((-b).val + b.val) M]
  rw [hzero, Nat.add_zero, pow_mul, clockMatrix_pow_card, one_pow]

/-- Every power of the cyclic update is unitary. -/
private theorem star_shiftMatrix_pow_mul (n : ℕ) :
    star (shiftMatrix M ^ n) * shiftMatrix M ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        star (shiftMatrix M ^ (n + 1)) * shiftMatrix M ^ (n + 1)
            = star (shiftMatrix M) *
                (star (shiftMatrix M ^ n) * shiftMatrix M ^ n) * shiftMatrix M := by
              rw [pow_succ, star_mul]
              noncomm_ring
        _ = 1 := by rw [ih, mul_one]; exact (window_unitary (M := M)).1

/-- Every power of the clock is unitary. -/
private theorem star_clockMatrix_pow_mul (n : ℕ) :
    star (clockMatrix M ^ n) * clockMatrix M ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        star (clockMatrix M ^ (n + 1)) * clockMatrix M ^ (n + 1)
            = star (clockMatrix M) *
                (star (clockMatrix M ^ n) * clockMatrix M ^ n) * clockMatrix M := by
              rw [pow_succ, star_mul]
              noncomm_ring
        _ = 1 := by rw [ih, mul_one]; exact (window_unitary (M := M)).2

/-- The adjoint of a shift power is the shift power at the negated index. -/
theorem star_shiftMatrix_pow (a : ZMod M) :
    star (shiftMatrix M ^ a.val) = shiftMatrix M ^ (-a).val := by
  have hright : shiftMatrix M ^ a.val * shiftMatrix M ^ (-a).val = 1 :=
    mul_eq_one_comm.mpr (shiftMatrix_pow_neg_mul a)
  calc
    star (shiftMatrix M ^ a.val)
        = star (shiftMatrix M ^ a.val) *
            (shiftMatrix M ^ a.val * shiftMatrix M ^ (-a).val) := by rw [hright, mul_one]
    _ = shiftMatrix M ^ (-a).val := by
          rw [← mul_assoc, star_shiftMatrix_pow_mul, one_mul]

/-- The adjoint of a clock power is the clock power at the negated index. -/
theorem star_clockMatrix_pow (b : ZMod M) :
    star (clockMatrix M ^ b.val) = clockMatrix M ^ (-b).val := by
  have hright : clockMatrix M ^ b.val * clockMatrix M ^ (-b).val = 1 :=
    mul_eq_one_comm.mpr (clockMatrix_pow_neg_mul b)
  calc
    star (clockMatrix M ^ b.val)
        = star (clockMatrix M ^ b.val) *
            (clockMatrix M ^ b.val * clockMatrix M ^ (-b).val) := by rw [hright, mul_one]
    _ = clockMatrix M ^ (-b).val := by
          rw [← mul_assoc, star_clockMatrix_pow_mul, one_mul]

/-- Adjoint law: conjugate-transposing a displacement word negates its index and multiplies
by the phase whose exponent is the product of the two original indices. -/
theorem displacement_adjoint (a b : ZMod M) :
    star (displacement M a b) =
      windowRoot M ^ (a * b).val • displacement M (-a) (-b) := by
  have hstar : star (displacement M a b)
      = clockMatrix M ^ (-b).val * shiftMatrix M ^ (-a).val := by
    rw [displacement, star_mul, star_clockMatrix_pow, star_shiftMatrix_pow]
  have hsplit : clockMatrix M ^ (-b).val * shiftMatrix M ^ (-a).val
      = displacement M 0 (-b) * displacement M (-a) 0 := by
    simp [displacement]
  rw [hstar, hsplit, displacement_mul]
  simp [mul_comm]

end

end D5.S3.Quantum.Algebra.WeylDisplacementAdjoint
