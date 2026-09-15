---
slug: oeis-a006068-kurkov-gray-inverse-recurrence
bibkey: kurkov2023a006068
doi: null
url: https://oeis.org/A006068
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence
---

# Kurkov's highest-bit recurrence for inverse Gray code

## Problem

OEIS A006068, NAME (`%N`, verbatim):

> a(n) is Gray-coded into n.

Mikhail Kurkov's conjecture (`%F`, verbatim):

> Conjecture: a(n) = a(A053645(A063946(n))) + A053644(n) for n > 0 with a(0) = 0. - _Mikhail Kurkov_, Sep 09 2023

The AUTHOR line (`%A`, verbatim) is:

> _N. J. A. Sloane_

Hanna's unconjectured XOR-prefix formula (`%F`, June 4, 2002) is:

> a(n) = n XOR [n/2] XOR [n/4] XOR [n/8] ... XOR [n/2^m] where m = [log(n)/log(2)] (for n>0) and [x] is integer floor of x.

His inverse formula (`%F`, January 18, 2012) is:

> a(n) XOR [a(n)/2] = n.

The exact formal result is:

```lean
(∀ n : ℕ, gray (a n) = n) ∧ a 0 = 0 ∧
∀ n : ℕ, 0 < n →
  a n = a (complementSecondBit n - msb (complementSecondBit n)) + msb n
```

Here `gray` is imported from the frozen
`D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm`.
The definition of `a` is Hanna's XOR-prefix formula written as the
recursion `n XOR a(n/2)`, terminating at zero. For positive inputs,
`msb n := 2 ^ Nat.log 2 n` is A053644, and subtraction of this value is
A053645. The totalized formula gives `msb 0 = 1`, while A053644(0) is 0;
every `msb` argument in the positive recurrence is positive.

The definition of `complementSecondBit` is A063946, fixing zero and one.
Its two arithmetic `%F` cases, proved and used inside `result`, are:

> If 2*2^k <= n < 3*2^k then a(n) = n + 2^k; if 3*2^k <= n < 4*2^k then a(n) = n - 2^k

## Motivation

Kurkov's conjecture describes inverse Gray code through its highest two
binary places. The result connects this recurrence to Hanna's independent
XOR-prefix definition and proves the inverse property for every natural
input. It settles the named external assertion over an unbounded domain.

## Gap

The orchestrator's 2026-09-15 readings report that OEIS still marks
Kurkov's `%F` line as "Conjecture", with no settlement line. The target
was preregistered in issue #7940, created 2026-09-14T22:11:25Z, before the
probe seat started. This is a first-tier external OEIS conjecture under
the small-conjecture route.

The same supplied readings report: arXiv API HTTP 429 at query time
(not searched); OpenAlex one unrelated hit, a Basque-language
Stern-sequence paper; MathOverflow zero hits; GitHub code search only
OEIS mirrors and one Python recipe; formal-conjectures zero hits.
The repository search before this addition found zero `A006068` hits;
the `Gray code` hits were confined to the frozen
`GrayCodeBinaryRecurrenceClosedForm` module in the A163617 lane.

The supplied probe search of pinned Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` found no inverse-Gray or
highest-bit recurrence theorem. `Nat.xor_range` concerns consecutive
integers, not the dyadic quotients used here. The frozen Gray module
supplies `gray`; its `yanev_a163617` theorem is a forward Gray-code
correction formula. No dominating theorem was found in those searched
scopes. These are attributed search results, not an exhaustive
literature search or a priority claim by this offline seat.

## Route

1. Define `a` by Hanna's recursion with termination on the natural input.
2. Use strong induction to prove commutation with division by two,
   inversion, and preservation of dyadic upper bounds.
3. Prove both arithmetic cases of the A063946 second-bit toggle and
   deduce that the highest bit is unchanged.
4. Compute the Gray code of the proposed right-hand side, then use
   the inverse identity to conclude Kurkov's recurrence. Treat `n=1`
   explicitly, and retain the zero initialization as a separate conjunct.

The public theorem has proof shape `content`, with escape-witness form
(2): its conclusion is produced on the live induction and highest-bit
proof path. Admission basis is `escape-witness`; the external problem
and its supplied preregistration also support `open-problem-resolution`.
The helpers are local facts within `result`, with no companion theorem
declarations. Utility is `none`: the result is an unbounded symbolic
identity, not a checker, numerical reduction, enumeration, or certified
finite instance.

## Falsifier

Any natural `n` with `gray (a n) ≠ n`, a nonzero value of `a 0`, or any
positive `n` violating the displayed Kurkov recurrence would contradict
the theorem. A violation of either quoted A063946 arithmetic case would
also contradict the corresponding local proof. The checked statement
quantifies over all naturals, beyond the experimental ranges.

## Evidence

- Single-file Lean compilation of
  `D5/S1/Digit/Admissibility/KurkovGrayInverseRecurrence.lean`: exit 0.
- Header check of the same module: exit 0.
- `#print axioms result`: `[propext, Classical.choice, Quot.sound]`.
- Deleting either direct import alone through process substitution makes
  single-file Lean compilation exit 1: removing the frozen Gray module
  loses `gray`; removing `Mathlib.Data.Nat.Log` loses `Nat.log` and its
  required lemmas. Both imports are retained.
- Direct kernel-profile run: exit 0, wall time 3.539384 seconds and
  cumulative type checking 143 milliseconds, on this arm64 worktree with
  Lean v4.33.0 and the warm import cache. Wall time was measured with a
  monotonic timer around the Lean process. RSS is unverified: the
  `/usr/bin/time -l` wrapper exited 1 after reporting
  `sysctl kern.clockrate: Operation not permitted`.
- The orchestrator reports `gray(a n)=n` and `a(gray n)=n` for
  `0 <= n < 2*10^5`, and zero Kurkov recurrence exceptions for
  `1 <= n < 50000`. The supplied probe reports zero exceptions below
  5000, including the inverse property and the two second-bit cases.
  These scans were not rerun in this seat and do not prove the universal
  statement.
- `make lean-report`, `make emit`, Scribe compilation/counts, emitted
  Markdown verification, `dotnet test`, deposit/cover, and whole-tree
  admission: not run in this seat (sandbox).

## Triage

`theorem`; resolution `proved`. The formal result proves the inverse
property, zero initialization, and Kurkov recurrence with its positive
guard. Stage A does not establish repository admission or freezing.

## ASSUMED-UNVERIFIED

The source quotations, authorship, issue #7940 timing, external gap
readings, and orchestrator/probe numerical results are supplied evidence.
No network check was made in this implementation seat. arXiv was not
searched because of HTTP 429; historical openness outside the checked
surfaces remains unverified. The bounded scans are fault-detection
evidence only. Scribe execution, emitted output, independent review,
admission, and freezing remain outside this seat's verified scope.
