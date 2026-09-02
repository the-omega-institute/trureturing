/- GID: D5/S1/Recurrence/NormOneLucasDouble
   generality: G
   mirror-B: D5/B/S1/Recurrence/NormOneLucasDouble
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: A norm-one conjugate pair doubles its trace by squaring, up to two. -/

/- Library-search audit trail (2026-09-02). Commands reproduced literally as run, each with the
   count it returned. Paths are relative to the delivery worktree.

   grep -rhoE '^ *(private )?(noncomputable )?(theorem|lemma|def|abbrev) +[A-Za-z0-9_.]*[Ll]ucas[A-Za-z0-9_.]*' D5 --include='*.lean' | wc -l
                                                                                             -> 28
     An earlier count of 19 was taken from a declaration-name dump that silently omitted private
     declarations; it is corrected here. Of the 28, nine are private. Twenty-four are tied to the
     golden instance: `goldenLucas`,
     `goldenLucasZ`, `golden_lucas_discriminant`, `golden_lucas_eq_trace_phi_pow`,
     `golden_fib_two_mul_eq_fib_mul_lucas`, `golden_lucas_succ_eq_fib_add_fib`,
     `pell_pm_four_iff_signed_lucas_fib`, plus occurrence-set gap classifications and a
     `LucasPair` growth-closure family. They are statements about `phi`, that is the single
     discriminant five, defined through powers and traces of `phi`. None is stated for an
     arbitrary conjugate pair. The four exceptions are the `symmetricLucasExtension` family
     (`symmetricLucasExtension`, `_binary`, `_canonical`, `_value`), which are generic `Finsupp`
     constructions carrying `Lucas` only in the name; they are not phi-specific and they state
     nothing about conjugate pairs. So the accurate claim is not that every Lucas declaration is
     phi-bound, but that every Lucas *identity* in this repository is.
   git grep -n 'digest:' origin/dev -- D5/S1/Scale/FibLucasDouble.lean D5/S1/Scale/Lucas.lean
     -> 2, read in full: "Fibonacci doubling is multiplication by the corresponding Lucas number"
     and "Lucas traces satisfy the Fibonacci bridge and Pell-type discriminant identity".
     Both are the golden instance.

   grep -ril "Lucas sequence" .lake/packages/mathlib --include='*.lean' | wc -l              -> 1
     That file is Mathlib/NumberTheory/EllipticDivisibilitySequence.lean, where the phrase occurs
     once inside a documentation comment noting that certain terms of Lucas sequences arise as
     elliptic divisibility sequences. It is neither a definition nor a theorem about them.
   grep -ril "LucasLehmer"    .lake/packages/mathlib --include='*.lean' | wc -l              -> 4
     Those are the Lucas-Lehmer primality test for Mersenne numbers and two Archive files using
     it for perfect numbers and Mersenne primes. That is a different object.
   grep -rnE "theorem.*[Ll]ucas.*two_mul|two_mul.*[Ll]ucas" .lake/packages/mathlib
     --include='*.lean' | wc -l                                                              -> 0
     Recorded first without -E, where `|` is a literal character rather than an alternation; the
     command above is the corrected form and was re-run to obtain this count.
   grep -ril "norm one unit" .lake/packages/mathlib --include='*.lean' | wc -l               -> 0
     The same four over batteries                                                 -> 0 each

   gh search prs --repo leanprover-community/mathlib4 --state open "Lucas sequence doubling"
     --limit 20                                                                              -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open "generalized Lucas"
     --limit 20                                                                              -> 0
   gh search code --repo leanprover/cslib "Lucas sequence" --limit 5                         -> 0
   gh search code --repo TauCetiProject/TauCeti "Lucas sequence" --limit 5                   -> 0

   Zulip was not queried for this statement, so that domain is absent rather than a negative.

   What the repository already has is the golden instance; what is absent everywhere searched is
   the statement for an arbitrary conjugate pair of norm one. The abstraction is taken here
   because a second instance has appeared in the source volume, not in advance of one.
-/

import Mathlib

/-!
# Doubling for a norm-one conjugate pair

Let two ring elements multiply to one. Their `n`-th power sum is a trace-like sequence, and the
difference of their `n`-th powers, divided by their difference, is the companion sequence. Squaring
the first sequence adds two to its value at twice the index; squaring the second, weighted by the
discriminant, subtracts two.

Both identities need only that the product of the pair is one. No ordering, positivity,
integrality, or specific discriminant is used, and none is claimed. The golden instance already
frozen in this repository is the case of discriminant five; nothing here asserts anything new about
that instance.
-/

namespace D5.S1.Recurrence.NormOneLucasDouble

variable {R : Type*} [CommRing R]

/-- Squaring the trace sequence adds two at twice the index. -/
theorem trace_sq_eq_trace_two_mul_add_two (a b : R) (hab : a * b = 1) (n : Nat) :
    (a ^ n + b ^ n) ^ 2 = (a ^ (2 * n) + b ^ (2 * n)) + 2 := by
  have hpow : a ^ n * b ^ n = 1 := by
    rw [← mul_pow, hab, one_pow]
  have hdouble : ∀ x : R, x ^ (2 * n) = (x ^ n) ^ 2 := by
    intro x
    rw [two_mul, pow_add, sq]
  rw [hdouble a, hdouble b]
  linear_combination 2 * hpow

/-- The companion sequence, weighted by the discriminant, subtracts two at twice the index. -/
theorem companion_sq_eq_trace_two_mul_sub_two (a b u : R) (hab : a * b = 1) (n : Nat)
    (hu : (a - b) * u = a ^ n - b ^ n) :
    (a - b) ^ 2 * u ^ 2 = (a ^ (2 * n) + b ^ (2 * n)) - 2 := by
  have hpow : a ^ n * b ^ n = 1 := by
    rw [← mul_pow, hab, one_pow]
  have hdouble : ∀ x : R, x ^ (2 * n) = (x ^ n) ^ 2 := by
    intro x
    rw [two_mul, pow_add, sq]
  have hsq : ((a - b) * u) ^ 2 = (a ^ n - b ^ n) ^ 2 := by rw [hu]
  rw [hdouble a, hdouble b]
  rw [mul_pow] at hsq
  linear_combination hsq - 2 * hpow

end D5.S1.Recurrence.NormOneLucasDouble
