/- GID: D5/S3/Quantum/Algebra/WeylDisplacementConjugation
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylDisplacementConjugation
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Conjugating one displacement word by another rescales it by the symplectic phase. -/

/- Library-search audit trail (2026-09-02). Commands reproduced literally as run, each with the
   count it returned. Paths are relative to the delivery worktree.

   A first pass searched documentation text with a bare `conjugat` alternative and was reported
   as five hits; that figure was a display limit, not a count. Re-run without truncation:

   git grep -clE "star \(displacement|displacement.*star \(displacement|conjugat" origin/dev
     -- 'D5/**/*.lean' | wc -l                                                             -> 178
     That regex matches prose, so it is too broad to settle anything. The searches below are at
     declaration level and are what the negative rests on.

   git grep -hoE "^(@\[[^]]*\][[:space:]]*)?(private )?(noncomputable )?(theorem|lemma|def)
     [A-Za-z0-9_']*displacement[A-Za-z0-9_']*(conj|star|sandwich|symplectic)[A-Za-z0-9_']*"
     origin/dev -- 'D5/**/*.lean'                                                            -> 1
     `critical_displacement_conjugation` in D5/S3/Weil/ZetaLinear/
     ReflectedZeroModePhaseFlattening.lean. Opened: it is complex conjugation of a critical-line
     parameter in analytic number theory. The name is nearly identical and the object is not.
   The reversed order returns `golden_subst_start_eq_displacement_decode` (substitution start
     versus Beatty displacement decode) and `star_displacement_of_two_torsion` (this family's
     two-torsion self-adjointness). Both opened; neither conjugates one word by another.

   git grep -clE 'displacement [^*]*\* *displacement [^*]*\* *star' origin/dev
     -- 'D5/**/*.lean' | wc -l                                                               -> 0
     No file states the sandwich form at all. This is the decisive negative.
   The four frozen Weyl modules export 18 public declarations, not the 16 first counted: a
   narrow `^theorem ` pattern silently omitted `noncomputable def displacement` and
   `@[simp] theorem displacement_zero`. All 18 were read, along with the 10 private helpers.
   The public ones are `displacement`, `displacement_zero`, `displacement_mul`,
   `displacement_sq`, `displacement_comm`, `displacement_two_anticommute`,
   `displacement_two_not_commute`, `shiftMatrix_pow_neg_mul`, `clockMatrix_pow_neg_mul`,
   `star_shiftMatrix_pow`, `star_clockMatrix_pow`, `displacement_adjoint`,
   `displacement_trace_eq_zero`, `displacement_trace_origin`, `displacement_trace`,
   `displacement_trace_orthogonal`, `star_displacement_of_two_torsion`,
   `two_torsion_overlap_conj`. None states a conjugation of one word by another.

   grep -rilE "Weyl.Heisenberg" .lake/packages/mathlib --include='*.lean' | wc -l           -> 0
   grep -rilE "displacement operator" .lake/packages/mathlib --include='*.lean' | wc -l     -> 0
   grep -rilE "symplectic character" .lake/packages/mathlib --include='*.lean' | wc -l      -> 0
   grep -rnE "theorem.*displacement.*(conj|star)" .lake/packages/mathlib --include='*.lean'
     | wc -l                                                                                -> 0

   Zulip was not queried for this statement, so that domain is absent rather than a negative.

   No upstream result is used beyond the frozen nodes this module imports; the phase bookkeeping
   is rebuilt here from `windowRoot_isPrimitiveRoot` because the corresponding helper in the
   frozen module is private and frozen modules are not amended.
-/

import D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

/-!
# Conjugating a displacement word by another

The composition law says two displacement words multiply up to a phase; the adjoint law says
conjugate-transposition negates an index up to a phase. Putting the two together, conjugating
`D (c, d)` by `D (a, b)` returns `D (c, d)` itself, rescaled by a single root of unity whose
exponent is the symplectic pairing `b * c - a * d` of the two indices.

The exponent is antisymmetric under swapping the two index pairs, which can be read off the
displayed statement. Nothing beyond that is claimed here: this module proves the phase identity
and states no consequence about when two words commute.
-/

namespace D5.S3.Quantum.Algebra.WeylDisplacementConjugation

open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

variable {M : ℕ} [NeZero M]

/-- The window root is an `M`-th root of unity, so its powers only see the exponent mod `M`.
The frozen module proves this for its own use behind `private`; it is rebuilt here rather than
amending a frozen file. -/
private theorem root_pow_mod (n : ℕ) :
    windowRoot M ^ (n % M) = windowRoot M ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n M]
  rw [pow_add, pow_mul, (windowRoot_isPrimitiveRoot M).pow_eq_one, one_pow, mul_one]

/-- Phases multiply by adding their indices in `ZMod M`. -/
private theorem root_pow_val_add (x y : ZMod M) :
    windowRoot M ^ (x + y).val = windowRoot M ^ x.val * windowRoot M ^ y.val := by
  rw [ZMod.val_add, root_pow_mod, pow_add]

/-- Conjugation law: conjugating `D (c, d)` by `D (a, b)` returns the same word scaled by the
phase whose exponent is the symplectic pairing `b * c - a * d`. -/
theorem displacement_conjugation (a b c d : ZMod M) :
    displacement M a b * displacement M c d * star (displacement M a b) =
      windowRoot M ^ (b * c - a * d).val • displacement M c d := by
  have hidx : displacement M (a + c + -a) (b + d + -b) = displacement M c d := by
    congr 1 <;> ring
  have hexp : b * c + (a * b + (b + d) * -a) = b * c - a * d := by ring
  calc displacement M a b * displacement M c d * star (displacement M a b)
      = (windowRoot M ^ (b * c).val • displacement M (a + c) (b + d)) *
          (windowRoot M ^ (a * b).val • displacement M (-a) (-b)) := by
        rw [displacement_mul, displacement_adjoint]
    _ = (windowRoot M ^ (b * c).val * windowRoot M ^ (a * b).val) •
          (displacement M (a + c) (b + d) * displacement M (-a) (-b)) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = (windowRoot M ^ (b * c).val * windowRoot M ^ (a * b).val) •
          (windowRoot M ^ ((b + d) * -a).val • displacement M c d) := by
        rw [displacement_mul, hidx]
    _ = (windowRoot M ^ (b * c).val *
          (windowRoot M ^ (a * b).val * windowRoot M ^ ((b + d) * -a).val)) •
          displacement M c d := by
        rw [smul_smul, mul_assoc]
    _ = windowRoot M ^ (b * c - a * d).val • displacement M c d := by
        rw [← root_pow_val_add, ← root_pow_val_add, hexp]

end D5.S3.Quantum.Algebra.WeylDisplacementConjugation
