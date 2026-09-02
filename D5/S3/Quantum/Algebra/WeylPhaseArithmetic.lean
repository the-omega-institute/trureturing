/- GID: D5/S3/Quantum/Algebra/WeylPhaseArithmetic
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylPhaseArithmetic
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Window-root powers see only the exponent modulo the window, so phases add indices. -/

/- Library-search audit trail (2026-09-03). Commands reproduced literally as run, each ending in
   `wc -l`; none is truncated. Declaration patterns are the wide form, so attribute-prefixed,
   private and `def` forms are included.

   P='^(@\[[^]]*\][[:space:]]*)?(private )?(noncomputable )?(theorem|lemma|def|abbrev) '

   git grep -hoE "${P}[A-Za-z0-9_']*windowRoot[A-Za-z0-9_']*" origin/dev -- 'D5/**/*.lean'
     | wc -l                                                                                 -> 7
     All seven opened and listed:
       WindowRegister.lean:22   noncomputable def windowRoot            (public, used here)
       WindowRegister.lean:26   theorem windowRoot_isPrimitiveRoot      (public, used here)
       WindowRegister.lean:38   private windowRoot_eq_character_one
       WindowRegister.lean:43   private windowRoot_pow_val_eq_character
       WeylDisplacement.lean:62 private windowRoot_pow_mod
       WeylDisplacementTrace.lean:86  private windowRoot_pow_val_inj
       WeylDisplacementTrace.lean:155 private windowRoot_pow_val_neg_mul
     Exactly two are public, and both are used here rather than reproved. The five private ones
     live inside frozen modules and cannot be imported; the fifth of them is propositionally the
     same statement as `windowRoot_pow_mod` below, which is why that lemma has to be re-derived
     rather than reused.

   The two statements proved here have therefore been derived three times in this repository
   already: privately inside the frozen `WeylDisplacement`, privately again inside
   `WeylDisplacementConjugation`, and once more in the first draft of `WeylDisplacementPowers`.
   This module is the single public home; later nodes import it instead of deriving a fourth.
   The frozen modules are not amended and their private copies stay exactly as frozen.

   grep -rlE "IsPrimitiveRoot.*pow_eq_one" .lake/packages/mathlib --include='*.lean' | wc -l
                                                                                             -> 1
     `Mathlib/RingTheory/RootsOfUnity/Basic.lean`, supplying `IsPrimitiveRoot.pow_eq_one`, which
     is the upstream result used rather than reproved.

   Batteries, CSLib and TauCeti were searched for earlier nodes of this family and returned
   nothing; no separate query was issued here, so those are carried negatives. Zulip was not
   queried, so that domain is absent rather than negative.
-/

import D5.S3.Observer.WindowRegister

/-!
# Phase arithmetic for the window root

Two facts are needed by every node that collects more than one window-root phase: powers of the
root see only the exponent modulo the window size, and two phases multiply by adding their
indices in `ZMod M`.

Both are elementary consequences of the root being primitive. They live in their own module,
below every node that uses them, so that there is one public source rather than a private copy
per consumer.
-/

namespace D5.S3.Quantum.Algebra.WeylPhaseArithmetic

open D5.S3.Observer.WindowRegister

variable {M : ℕ} [NeZero M]

/-- Powers of the window root depend only on the exponent modulo `M`. -/
theorem windowRoot_pow_mod (n : ℕ) :
    windowRoot M ^ (n % M) = windowRoot M ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n M]
  rw [pow_add, pow_mul, (windowRoot_isPrimitiveRoot M).pow_eq_one, one_pow, mul_one]

/-- Phases multiply by adding their indices in `ZMod M`. -/
theorem windowRoot_pow_val_add (x y : ZMod M) :
    windowRoot M ^ (x + y).val = windowRoot M ^ x.val * windowRoot M ^ y.val := by
  rw [ZMod.val_add, windowRoot_pow_mod, pow_add]

end D5.S3.Quantum.Algebra.WeylPhaseArithmetic
