---
slug: hanna-nested-square-odd-coefficients
bibkey: hanna2026a392210
doi: null
url: https://oeis.org/A392210
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/NestedSquareOddEven.result
---

# The Nested-Square Generating Function Has Even Coefficients at Odd Indices

## Problem

OEIS A392210, by Paul D. Hanna, Feb 02 2026:

> G.f.: x + sq(x/(1-x) + sq(x/(1-2*x) + sq(x/(1-3*x) + sq(x/(1-4*x) + ...)))) where sq(x) = x^2, an
> infinitely nested square.

The comment carrying the question:

> It appears that a(2*n-1) is even for n > 1.

## Motivation

The frozen theorem `D5/S1/Recurrence/Parity/NestedSquareOddEven.result` settles the comment for every
solution of the entry's functional equation `A(x) = x + A(x/(1-x))^2`, and shows that a solution
exists.

## Gap

Issue 9657 records the screen carried out before the work. The A-number appears nowhere under
`Problems/`, `D5/`, `Library/` or `Blueprint/`, nor in the screening records, nor in
google-deepmind/formal-conjectures. The entry records no proof and no reference; its cross-references
state no parity result for this sequence, and a catalogue search by the terms returns only this entry.
This is a bounded negative finding.

## Route

**One.** Write `F = A(x/(1-x))`. The coefficient of `x^(2m+1)` in `F^2` is `Σ_{i=0}^{2m+1} f_i f_(2m+1-i)`.
Split the range into `i ≤ m` and `i ≥ m+1`; reflecting the second half by `i ↦ 2m+1-i` turns it into the
first, so the sum is twice `Σ_{i=0}^{m} f_i f_(2m+1-i)`.

**Two.** For `n > 1` put `2n-1 = 2m+1` with `m ≥ 1`. The term `x` contributes nothing at that index, so
the coefficient of `A` there equals that of `F^2`, which is even by step one.

**Three.** A solution exists. Define `a(0) = 0`, `a(1) = 1` and, for `n ≥ 2`,
`a(n) = Σ_{k=1}^{n-1} b(k) b(n-k)` with `b(m) = Σ_{k=1}^{m} C(m-1, k-1) a(k)`, the entry's own recurrence.
Since `(x/(1-x))^k` has coefficient `C(m-1, k-1)` at `x^m`, substituting `x/(1-x)` into `Σ a(k) x^k` gives
`Σ b(m) x^m`, and comparing coefficients of `x + (Σ b(m) x^m)^2` with `Σ a(n) x^n` gives the equation.

## Falsifier

The statement would fail if some odd-index coefficient were odd. Reading the index as `2n+1` with
`n ≥ 1` changes nothing; reading it as `2n-1` with `n ≥ 1` would include `a(1) = 1`, which the comment
excludes by requiring `n > 1`.

## Evidence

The entry's recurrence reproduces its first twelve terms, and iterating the functional equation on
truncated power series reproduces the same twelve terms independently. The coefficients `a(3)` through
`a(39)` at odd indices are all even.

## Triage

`theorem`; Tier 1 named external open question from 2026, preregistered in issue 9657 before the work.
The computational use is `none`: the delivered statement quantifies over every solution and every
index.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full and records no proof and no reference to
one. Citation indices, printed sources and the resolved set of arXiv:2608.11941 were not exhaustively
compared, so no worldwide priority claim is made. The weight is stated plainly: the argument is a
symmetry of the square, and what is settled is that the sentence sat on the entry unjudged.
