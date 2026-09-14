---
slug: oeis-a059894-stephan-complement-reverse-recurrence
bibkey: stephan2003a059894
doi: null
url: https://oeis.org/A059894
triage: theorem
motivation_gids:
  - D5/S1/Digit/StephanComplementReverseRecurrence
---

# Stephan's A059894 complement-reversal conjectures

## Problem

OEIS A059894, NAME (`%N`, verbatim):

> Complement and reverse the order of all but the most significant bit in binary expansion of n. n = 1ab..yz -> 1ZY..BA = a(n), where A = 1-a, B = 1-b, ... .

Ralf Stephan's recurrence conjecture (`%F`, verbatim):

> a(1) = 1, a(2n) = a(n) + 2^(floor(log_2(n))+1), a(2n+1) = a(n) + 2^floor(log_2(n)) (conjectured). - _Ralf Stephan_, Aug 21 2003

Ralf Stephan's digit-count conjecture (`%F`, verbatim):

> A000120(a(n)) = A000120(A054429(n)) = A023416(n) + 1 (conjectured). - _Ralf Stephan_, Oct 05 2003

AUTHOR (`%A`, verbatim):

> _Marc LeBrun_, Feb 06 2001

The definition `a` applies the quoted transformation to the little-endian
list `Nat.digits 2 n`: drop its last entry, reverse the remaining list, map
natural subtraction `1 - d`, append `[1]`, and evaluate with `Nat.ofDigits 2`.
The definition `complementRest` omits only the reversal and represents A054429
on positive inputs. A000120 counts one bits and A023416 counts zero bits in
the positive canonical binary expansion.

The literal theorem statement is:

```lean
a 1 = 1 ∧
(∀ n : ℕ, 0 < n → a (2 * n) = a n + 2 ^ (Nat.log 2 n + 1)) ∧
(∀ n : ℕ, 0 < n → a (2 * n + 1) = a n + 2 ^ (Nat.log 2 n)) ∧
(∀ n : ℕ, 0 < n →
  (Nat.digits 2 (a n)).count 1 = (Nat.digits 2 (complementRest n)).count 1 ∧
  (Nat.digits 2 (a n)).count 1 = (Nat.digits 2 n).count 0 + 1)
```

Here `Nat.log 2 n` agrees with the floor of the base-two logarithm on the
positive domain. The counting and recurrence clauses have the explicit
guard `0 < n`; no such clauses at zero are asserted.

## Motivation

The independent question is whether the two published Stephan formula lines
hold for every positive input, starting from the literal bit transformation.
The orchestrator identifies issue #7903 as their pre-probe registration.
The delivery uses `admission_basis: open-problem-resolution`; its sole
theorem is honestly classified `proof_shape: bind-only`, with no escape
witness or companion theorem. Utility is `none`: the result is an unbounded
symbolic identity, not a finite certified instance, enumeration, checker,
or numerical reduction.

## Gap

The following pre-registration and literature-check facts are supplied by
the orchestrator; this offline fix seat did not independently verify them:

Pre-registration issue #7903 (opened 2026-09-14T20:03:25Z, before the probe seat started at 2026-09-14T20:06:12Z) classifies the target as tier one (a 2003 OEIS `%F` conjecture, open because unexamined) and records the literature check: OEIS text still marks both lines conjectured with no settlement line; arXiv API 0 entries; OpenAlex 0; MathOverflow 1 unrelated thread (455692, a different composition conjecture); GitHub code search only OEIS mirrors; formal-conjectures 0; repository prior-art 0 hits; independent numerics 1 ≤ n < 20000 zero exceptions.

The supplied probe found no exact target theorem in pinned Mathlib; its
digit and list lemmas jointly supply the required binding proof. These
bounded search readings do not establish exhaustive literature coverage or
priority.

## Route

1. Evaluate the definition at one using the binary digit lemmas.
2. Apply `Nat.digits_base_mul` and `Nat.digits_add` to the even and odd
   inputs. List reversal, mapping, and `Nat.ofDigits_append` reduce the
   recurrences to arithmetic; `Nat.length_digits` supplies the logarithm.
3. Apply `Nat.digits_ofDigits` to reconstruct each complemented digit list.
   Counting after complementation converts the count of ones into the
   original count of zeros; reversal preserves that count.
4. The original leading binary digit is one by the upstream digit bound and
   nonzero-last-digit theorem. Removing it preserves the zero count, and
   restoring `[1]` adds one to the transformed one count.

All local facts remain within `result`. The proof directly instantiates
pinned upstream lemmas and normalizes the resulting list and arithmetic
expressions. It introduces no separate mathematical helper declaration.

The review judgement is `proof_shape: bind-only` for `result`: all steps
are instantiations of pinned `Nat.digits`/`Nat.ofDigits` lemmas plus
normalisation. `admission_basis: open-problem-resolution` applies under
CLAUDE.md §3.2. With the pre-registration and PR-body facts supplied by the
orchestrator, all four conditions (a)–(d) are met:

- (a) The delivery surface is the two necessary definitions, `a` and
  `complementRest`, and one `result`.
- (b) The shape is reported honestly here and in the PR body; the PR-body
  fact is supplied by the orchestrator.
- (c) Scribe carries `OpenProblemResolutionClaim` (`Proved`) and links this
  Problems dossier.
- (d) `utility: none`: no declaration has computational content; the result
  is an unbounded symbolic identity.

## Falsifier

A failure of `a 1 = 1`, or a positive natural input violating either
recurrence or either digit-count equality, would contradict the theorem.
Finite numerical agreement alone does not prove the unbounded statement.

## Evidence

- Lean module: `D5/S1/Digit/StephanComplementReverseRecurrence.lean`.
- `lake env lean` on the final module: bare exit 0. The definitions and
  complete proof are byte-for-byte copies of the verified probe.
- `tools/scripts/agent/header-check.sh` on the module: bare exit 0.
- `#print axioms result` gives exactly
  `[propext, Classical.choice, Quot.sound]`; both definitions have the same
  measured closure. The axiom-print compilation exits 0.
- The sole direct import is `Mathlib.Data.Nat.Digits.Lemmas`. Deleting it
  alone by process substitution makes Lean exit 1. Deleting the redundant
  `Mathlib.Data.List.Count` import exited 0, so that import was removed.
- Kernel profile with `-Dprofiler=true -Dtrace.profiler.threshold=1000` and
  `/usr/bin/time -p`: bare exit 0, 7.94 seconds wall time and 24.2 milliseconds
  type checking, on Lean 4.33.0, arm64 macOS, using the warm lane cache.
- RSS is unavailable: `/usr/bin/time -l` exited 1 after the sandbox denied
  `sysctl kern.clockrate`. This failed instrumentation run is not counted
  as a successful check.
- Lean report, Scribe counts, Markdown emission, .NET tests, deposit, cover,
  and repository admission: not run in this seat (sandbox).
- The orchestrator's finite scan is corroboration only; it is not a proof
  premise.

## Triage

`theorem`; resolution `proved`. The two published conjectures are proved in
the displayed positive-input formalization. The judgement is
`proof_shape: bind-only` for `result` and
`admission_basis: open-problem-resolution` under CLAUDE.md §3.2,
pre-registration #7903. Conditions (a)–(d) are met as detailed in Route,
using the orchestrator-supplied pre-registration and PR-body facts. No novel
proof steps are claimed.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and priority are not established by the
supplied bounded search readings. Neither is claimed by this delivery.
