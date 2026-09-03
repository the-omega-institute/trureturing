/- GID: D5/S1/Recurrence/NormOneTraceAddition
   generality: G
   mirror-B: D5/B/S1/Recurrence/NormOneTraceAddition
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Norm-one power sums obey a shift-by-two addition law without index subtraction. -/

/- Library-search audit trail (2026-09-03). Commands reproduced literally as run, each ending in
   `wc -l`; none truncated. Declaration patterns are the wide form. Where names are listed, the
   list is the output of the same command that produced the count, not a recollection.

   P='^(@\[[^]]*\][[:space:]]*)?(private )?(noncomputable )?(theorem|lemma|def|abbrev) '

   git grep -clE '\^ \(m \+ n\) \+ [a-z] \^ \(m \+ n\)' origin/dev -- 'D5/**/*.lean' | wc -l -> 0
   git grep -clE '\^ \(n \+ 2\) \+ [a-z] \^ \(n \+ 2\)' origin/dev -- 'D5/**/*.lean' | wc -l -> 0
     No file states a power-sum addition law or a two-step power-sum recurrence directly.

   git grep -hoE "${P}[A-Za-z0-9_']*(trace|lucas)[A-Za-z0-9_']*add[A-Za-z0-9_']*" origin/dev
     -- 'D5/**/*.lean' | wc -l                                                              -> 12
     All twelve listed and read. Eleven are different objects: C*-algebra trace additivity
     (`cstar_trace_add`, three occurrences), partial traces on records, phase-enriched core
     trace gaps, a golden-specific Lucas/Fibonacci bridge, and `rtrace_add`, which is additivity
     of a rank-trace. The twelfth matters and is recorded below.

   Exactly one declaration in this repository is an instance of what is proved here.
     `trace_sq_eq_trace_two_mul_add_two`, frozen in D5/S1/Recurrence/NormOneLucasDouble.lean,
     is the case `m = 0`: setting `m = 0` gives `T (2n) = T n * T n - T 0`, and with `T 0 = 2`
     that rearranges to its `(a^n + b^n)^2 = (a^(2n) + b^(2n)) + 2`. It is not restated or
     amended here.
     One further declaration is related but is NOT an instance, and is recorded to say so.
     `free_transfer_trace_add_two`, private in
     D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.lean, reads
     `trace (M ^ (N+2)) = 2y * trace (M ^ (N+1)) - trace (M ^ N)` for a real transfer matrix
     whose determinant that file proves to be one. The shapes match, but this module quantifies
     over scalars `a b : R` with `a * b = 1` and offers no matrix, trace or characteristic-root
     interface. Identifying `trace (M ^ k)` with `a ^ k + b ^ k` for the characteristic roots
     would need a bridge that is not proved here, and that file proves its recurrence
     independently. So it is an analogy, not a specialisation, and this module claims no
     relationship to it beyond resemblance. Supplying that bridge is a separate piece of work.

   grep -rlE "theorem.*(rec.*unique|unique.*recurrence|eq_of_.*rec)" .lake/packages/mathlib
     --include='*.lean' | wc -l                                                              -> 9
     All nine opened: they are in Topology, Analysis and QPF/PFunctor files and concern germs,
     locally constant maps, covering spaces, analytic continuation, affine subspaces and
     coinductive fixed points. None is a second-order recurrence result.

   Batteries, CSLib and TauCeti were searched for earlier nodes of this family and returned
   nothing; no separate query was issued here, so those are carried negatives rather than fresh
   ones. Zulip was not queried, so that domain is absent rather than negative.
-/

import D5.S1.Recurrence.NormOneLucasDouble

/-!
# An addition law for norm-one power sums

Write `T k = a ^ k + b ^ k` for a pair with `a * b = 1`. The law below shifts by twice a step:

`T (m + 2 * n) = T (m + n) * T n - T m`

It is stated this way to avoid subtracting indices, which would need truncated subtraction on
`Nat`. Two cases already appear in this repository — `m = 0` is the frozen doubling identity in
`NormOneLucasDouble`, and `n = 1` is the two-step recurrence, which a private lemma in the
Chebyshev transfer-matrix file proves at one concrete matrix. Both are recorded in the audit
trail above; neither file is touched.

The recurrence itself is included below as the `n = 1` corollary, since that is the form a
consumer reaches for.
-/

namespace D5.S1.Recurrence.NormOneTraceAddition

variable {R : Type*} [CommRing R]

/-- Addition law: shifting by `2 * n` multiplies by the trace at `n` and subtracts the
unshifted term. -/
theorem trace_add_two_mul (a b : R) (hab : a * b = 1) (m n : Nat) :
    a ^ (m + 2 * n) + b ^ (m + 2 * n)
      = (a ^ (m + n) + b ^ (m + n)) * (a ^ n + b ^ n) - (a ^ m + b ^ m) := by
  have hpow : a ^ n * b ^ n = 1 := by
    rw [← mul_pow, hab, one_pow]
  have hsplit : m + 2 * n = m + n + n := by
    omega
  rw [hsplit]
  simp only [pow_add]
  linear_combination (-(a ^ m + b ^ m)) * hpow

/-- The two-step recurrence, the case `n = 1`. -/
theorem trace_recurrence (a b : R) (hab : a * b = 1) (m : Nat) :
    a ^ (m + 2) + b ^ (m + 2)
      = (a + b) * (a ^ (m + 1) + b ^ (m + 1)) - (a ^ m + b ^ m) := by
  have h := trace_add_two_mul a b hab m 1
  simpa [mul_comm] using h

end D5.S1.Recurrence.NormOneTraceAddition
