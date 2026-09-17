---
slug: oeis-a090079-yanev-run-compression-closed-form
bibkey: yanev2016a090079
doi: null
url: https://oeis.org/A090079
triage: theorem
motivation_gids:
  - D5/S1/Digit/YanevRunCompressionClosedForm
---

# Yanev's closed form for binary run compression

## Problem

OEIS A090079, NAME (`%N`, verbatim):

> In binary expansion of n: reduce contiguous blocks of 0's to 0 and contiguous blocks of 1's to 1.

Yanev's FORMULA conjecture (`%F`, verbatim):

> Conjecture: a(n) = (2^(A005811(n)+1) + (1-(-1)^n)/2 - 2)/3. - _Velin Yanev_, Dec 12 2016

The AUTHOR line (`%A`, verbatim):

> _Reinhard Zumkeller_, Nov 20 2003

The proved statement is
`forall n : Nat, 3 * a n = 2 ^ (runs n + 1) + n % 2 - 2`, where
`runs n = ((Nat.digits 2 n).splitBy (· == ·)).length` and
`a n = Nat.ofDigits 2 (((Nat.digits 2 n).splitBy (· == ·)).map List.head!)`.
The list is little-endian; reversing a word preserves its run count and
reverses the order of its compressed digits. Thus these definitions implement
the literal operation. The number of binary runs is the quantity A005811(n)
used in the conjecture. The integer identity `(1-(-1)^n)/2 = n mod 2`
identifies the parity term. The statement is multiplied by 3 to stay in ℕ.
For positive n the numerator is nonnegative; at zero both sides are zero.
Lean subtraction is truncated natural subtraction.

## Motivation

The value of the compressed binary word depends only on its number of runs
and its least significant digit. The theorem gives that dependence for every
natural number, including zero, using the literal compression algorithm.

## Gap

The orchestrator supplied the following facts and readings on 2026-09-15:
pre-registration issue #7905 opened at 2026-09-15 04:00Z, before the probe
seat; this is a tier-one external open problem, the 2016 OEIS `%F`
conjecture. OEIS text still marks the formula line Conjecture; the arXiv
API query `all:"A090079"` returned 0 entries; OpenAlex returned 0;
MathOverflow returned 0; GitHub code search found only OEIS mirrors;
formal-conjectures returned 0. Repository prior-art search found `A090079`
only in an xref list of a triage note and `A005811` had 0 hits. Independent
numerics for `1 ≤ n < 20000` had zero exceptions. These are attributed
orchestrator readings, not searches or computations performed by this
offline fix seat, and do not establish exhaustive novelty.

The probe's local repository and pinned-Mathlib search found digit and
splitBy invariants but no theorem evaluating arbitrary alternating binary
words. Its broader Yanev matches concern A163617. No frozen project theorem
is imported by this module.

## Route

1. Establish the local `have alternating_value` identity inside `result` by
   induction on an arbitrary binary list with unequal adjacent entries and
   last digit one:
   `3 * Nat.ofDigits 2 l + 2 = 2 ^ (l.length + 1) + l.head!`.
2. Use the splitBy API to show that the heads of the maximal constant blocks
   form such a list when n is nonzero. Its length is `runs n`, and its head
   is `n % 2`.
3. Apply the invariant and rearrange natural arithmetic. Discharge n=0
   directly from the empty digit list.

`result` has `proof_shape: bind-only`: the alternating-list evaluation
identity follows from the pinned digit and `splitBy` APIs by instantiation
and normalisation, including after the local proof is inlined. No escape
witness is claimed. `runs` and `a` have `proof_shape: definition`.

The `admission_basis: open-problem-resolution` is CLAUDE.md §3.2's external
open-problem exception, with its four conditions:

(a) The declaration surface is exactly the definitions `runs`, `a` and the
single theorem `result`; there is no private or public companion theorem.
(b) The proof shape of `result` is reported honestly as `bind-only`.
(c) The Scribe theorem node carries `OpenProblemResolutionClaim` with
`ResolutionKind.Proved` and references this Problems dossier.
(d) `utility: none` applies: the definitions and symbolic proof do not
deliver bounded enumerations, certified instances, a checker, or a numerical
reduction. The independently named question answered is Yanev's formula,
pre-registered in #7905.

## Falsifier

A natural n whose literal binary run compression violates the displayed
identity would contradict the theorem. The theorem quantifies over every
natural n; bounded numerical agreement alone cannot establish it.

## Evidence

- Lean module: `D5/S1/Digit/YanevRunCompressionClosedForm.lean`.
- Single-file `lake env lean`: exit 0 in this seat.
- `tools/scripts/agent/header-check.sh` on that module: exit 0 in this seat.
- A single-file diagnostic copy with `#print axioms` exits 0. The axiom
  closure of each public declaration is exactly
  `[propext, Classical.choice, Quot.sound]`. `alternating_value` is a local
  `have` inside `result`, not a separate theorem declaration.
- Deleting `Mathlib.Data.Nat.Digits.Lemmas` alone via process substitution
  gives Lean exit 1, with missing digit definitions. Deleting
  `Mathlib.Data.List.SplitBy` alone gives exit 1, with missing block lemmas.
  Both direct imports are individually necessary.
- `lake env lean -Dprofiler=true -Dtrace.profiler.threshold=1000` on the
  module exits 0: wall time 10.507940 seconds, type checking 46.9 milliseconds,
  Lean 4.33.0 on this warm-cache worktree. Wall time is measured with a
  monotonic clock around the Lean subprocess. RSS is unverified: no RSS
  measurement was run in this fix seat.
- The orchestrator reports independent numerics for `1 <= n < 20000` with
  zero exceptions. This bounded reading supports fault detection only.
- Full-tree Lean report, Scribe counts, emitted Markdown check, .NET tests,
  deposit, and cover: not run in this seat (sandbox).
- Git commit: not run in this seat; these source files are uncommitted.

## Triage

`theorem`; resolution `proved` for the formal statement at every natural n.
Repository admission, freezing, and the independent mirror review remain
outside this implementation seat.

## ASSUMED-UNVERIFIED

The external OEIS quotations, A005811 identification, current literature
status, issue #7905 pre-registration, and the orchestrator's search and
numerical readings were supplied in the brief and were not rechecked over
the network in this seat. Historical openness outside those searched
surfaces and publication priority are unverified. Single-file kernel
verification does not constitute full harness admission or a completed
Scribe emission check.
