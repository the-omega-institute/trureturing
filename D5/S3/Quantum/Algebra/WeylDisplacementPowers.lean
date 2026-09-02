/- GID: D5/S3/Quantum/Algebra/WeylDisplacementPowers
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylDisplacementPowers
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The nth power of a displacement word carries the triangular Weyl cocycle phase. -/

/- Library-search audit trail (2026-09-02). Commands reproduced literally as run, each with the
   count it returned. Counts end in `wc -l`; none is truncated by `head`. Declaration patterns
   are the wide form, so attribute-prefixed, private and `def` forms are included.

   P='^(@\[[^]]*\][[:space:]]*)?(private )?(noncomputable )?(theorem|lemma|def|abbrev) '

   git grep -hoE "${P}[A-Za-z0-9_']*displacement[A-Za-z0-9_']*(pow|power|iterate|choose)
     [A-Za-z0-9_']*" origin/dev -- 'D5/**/*.lean' | wc -l                                    -> 0
   The reversed order, `(pow|choose)` before `displacement`, also returns 0.

   git grep -clE 'displacement M [a-z] [a-z] \^ ' origin/dev -- 'D5/**/*.lean' | wc -l       -> 1
     That one file is WeylDisplacement.lean itself, holding `displacement_sq`, the `n = 2`
     case. It is opened below and is the reason this node is a generalisation rather than a
     duplicate.
   git grep -clE 'choose 2' origin/dev -- 'D5/S3/Quantum/**/*.lean' | wc -l                  -> 0
   grep -rlE "theorem.*displacement.*pow|Weyl.*cocycle" .lake/packages/mathlib
     --include='*.lean' | wc -l                                                              -> 0

   Batteries, CSLib and TauCeti were searched for the earlier nodes of this family and returned
   nothing; no separate query was issued here, so those are carried negatives rather than fresh
   ones. Zulip was not queried, so that domain is absent rather than negative.

   The phase arithmetic used here is imported from the sibling module `WeylPhaseArithmetic`,
   which is introduced alongside this one. The frozen `WeylDisplacement` keeps its own private
   copy; that file is not amended.

   Relation to the frozen `displacement_sq`. That result states
   `displacement M a b ^ 2 = windowRoot M ^ (a * b).val • displacement M (a + a) (b + b)`.
   It is the `n = 2` instance of the law proved here, since `Nat.choose 2 2 = 1`. It stays
   exactly as frozen; nothing about it is restated or amended, and this module does not import
   any claim from it.
-/

import D5.S3.Quantum.Algebra.WeylDisplacement
import D5.S3.Quantum.Algebra.WeylPhaseArithmetic

/-!
# Powers of a displacement word

Composing a displacement word with itself `n` times lands on the `n`-fold index and accumulates
one phase per composition. The accumulated exponent is the triangular number `n.choose 2` times
the product of the two indices, because the `k`-th composition contributes `k * a * b` and those
contributions sum to `(0 + 1 + ... + (n-1)) * a * b`.

The phase arithmetic this proof needs — that window-root powers see only the exponent modulo
`M`, and that phases multiply by adding indices — is imported from `WeylPhaseArithmetic` rather
than re-derived here. The frozen `WeylDisplacement` module holds a private copy that cannot be
imported, and frozen modules are not amended; that private copy stays exactly as frozen.
-/

namespace D5.S3.Quantum.Algebra.WeylDisplacementPowers

open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylPhaseArithmetic

variable {M : ℕ} [NeZero M]

/-- Power law: the `n`-th power of a displacement word is the word at the `n`-fold index,
scaled by the phase whose exponent is `n.choose 2` times the product of the indices. -/
theorem displacement_pow (a b : ZMod M) (n : ℕ) :
    displacement M a b ^ n =
      windowRoot M ^ (((n.choose 2 : ℕ) : ZMod M) * a * b).val •
        displacement M ((n : ZMod M) * a) ((n : ZMod M) * b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hchoose : ((n + 1).choose 2 : ℕ) = n.choose 2 + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
    have hidx : ∀ x : ZMod M, (n : ZMod M) * x + x = ((n + 1 : ℕ) : ZMod M) * x := by
      intro x; push_cast; ring
    have hexp : ((n.choose 2 : ℕ) : ZMod M) * a * b + (n : ZMod M) * b * a
        = (((n + 1).choose 2 : ℕ) : ZMod M) * a * b := by
      rw [hchoose]; push_cast; ring
    rw [pow_succ, ih, Matrix.smul_mul, displacement_mul, smul_smul,
      ← windowRoot_pow_val_add, hexp, hidx, hidx]

end D5.S3.Quantum.Algebra.WeylDisplacementPowers
