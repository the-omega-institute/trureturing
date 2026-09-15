---
slug: oeis-a051903-yanev-max-exponent-radical-recurrence
bibkey: yanev2017a051903
doi: null
url: https://oeis.org/A051903
triage: theorem
motivation_gids:
  - D5/S3/Arith/YanevMaxExponentRadicalRecurrence
---

# Yanev's maximum prime exponent recurrence

## Problem

OEIS A051903, NAME (`%N`, verbatim):

> Maximum exponent in the prime factorization of n.

Velin Yanev's FORMULA conjecture (`%F`, verbatim):

> Conjecture: a(n) = a(A003557(n)) + 1. This relation together with a(1) = 0 defines the sequence. - _Velin Yanev_, Sep 02 2017

AUTHOR (`%A`, verbatim):

> _Labos Elemer_, Dec 16 1999

With `a n := n.primeFactors.sup n.factorization` and the frozen
`D5/S1/Deficit/AlmostAdditivity.primeRadical`, the literal theorem is

```lean
a 1 = 0 ∧ (∀ n : ℕ, 1 < n → a n = a (n / primeRadical n) + 1) ∧
  ∀ b : ℕ → ℕ, b 1 = 0 → (∀ n : ℕ, 1 < n → b n = b (n / primeRadical n) + 1) →
    ∀ n : ℕ, 0 < n → b n = a n
```

Here primeRadical is A007947, and A003557(n) = n / primeRadical(n) on the positive sequence
domain. The quotient uses natural-number division. The empty supremum gives
`a 0 = 0`, an out-of-range extension; no recurrence at zero or one is claimed.

The third conjunct formalizes the %F line's second sentence: the relation
together with `a(1) = 0` determines the sequence on positive indices. Every
natural-valued function `b` with the same base value and recurrence agrees with
`a` at every positive index; its value at zero is unrestricted.

## Motivation

Yanev's conjecture characterizes maximum prime multiplicity by repeatedly
removing one copy of every prime divisor. The independent question and exact
guarded statement were pre-registered in issue #7926 before the probe, as
reported by the orchestrator.

## Gap

According to the orchestrator's 2026-09-15 literature readings, the OEIS text
still marks the %F line "Conjecture" and has no settlement line. Sela Fried's "Proofs of some
conjectures of Yanev" (2025, OEIS-linked `a006519.pdf`) has Theorems 1–3 on
A000188, A006519, and A001157; it does not cover A051903.

Those readings report that the arXiv API returned HTTP 429/503 at query time and was not searched.
OpenAlex returned one unrelated hit; MathOverflow returned zero. GitHub code
search found only OEIS mirrors, and formal-conjectures returned zero. The
repository prior-art check found `A051903` only in an xref list of a triage
note. These readings do not establish exhaustive literature coverage or
global priority.

The repository's frozen `D5/S1/Deficit/AlmostAdditivity.primeRadical` (the same product of distinct prime factors) is reused; no statement of this conjecture exists in the repository.

The probe's pinned-Mathlib statement search found no exact whole-statement
declaration in its searched scope. The proof directly uses
Mathlib's product-factorization, quotient-factorization, finite-support, and
finite-supremum APIs.

## Route

1. The empty prime-factor set at one gives the base value.
2. The product of distinct prime divisors divides n and has exponent one at
   each prime in n's support.
3. Quotient factorization subtracts that exponent. The quotient's support is
   contained in the original support; extending by zero preserves the maximum.
4. For `n > 1` the original support is nonempty and every supported exponent
   is positive. Commuting addition with its finite supremum proves the recurrence.
5. For `n > 1`, a prime divisor is greater than one and divides the positive
   radical, so `1 < primeRadical n`. Since the radical divides `n`, the quotient
   is positive and strictly smaller than `n`. Strong induction proves that any
   `b : ℕ → ℕ` with `b 1 = 0` and the same recurrence agrees with `a` at every
   positive index, giving the third conjunct inside `result`.

The proof is `bind-only`: the recurrence uses existing Mathlib applications,
logical composition, and normalization, and determination combines the two
recurrences by routine strong induction. Its `admission_basis` is
`open-problem-resolution` under pre-registration #7926, with no escape witness.
The public surface contains only the definition `a` and theorem `result`; all
intermediate facts are local to the theorem. The utility classification is
`none`: this definition and the unbounded symbolic theorem are neither a
bounded enumeration, a checker, a numeric reduction, nor a certified finite
instance.

## Falsifier

A nonzero base value `a 1`, a natural number `n > 1` with
`a n ≠ a (n / primeRadical n) + 1`, or a function `b : ℕ → ℕ` satisfying
`b 1 = 0` and `∀ n : ℕ, 1 < n → b n = b (n / primeRadical n) + 1` but
disagreeing with `a` at some positive index would contradict the displayed
theorem. The guard is essential to the intended sequence recurrence, which is
not asserted at zero or one; determination does not constrain `b 0`.

## Evidence

The proof uses symbolic prime-factorization and finite-supremum identities
for every natural `n > 1`, followed by strong induction for determination on
positive indices.

The orchestrator reports zero exceptions for `2 ≤ n ≤ 3000`; the probe
reports zero exceptions for `2 ≤ n ≤ 5000`. These finite scans are not
premises of the universal Lean theorem.

## Triage

`theorem`; resolution `proved`. The kernel-checked conclusion is the base
value, Yanev's recurrence for every natural `n > 1`, and determination of the
sequence on all positive indices by that base value and recurrence.
Repository admission and freeze are not established by this mathematical result.

## ASSUMED-UNVERIFIED

The exact OEIS quotations, issue #7926 pre-registration, literature readings,
and numeric scans are attributed to the orchestrator and probe. Historical
openness beyond the checked surfaces, including the unavailable arXiv search,
is unverified. No exhaustive literature or priority claim is made.
