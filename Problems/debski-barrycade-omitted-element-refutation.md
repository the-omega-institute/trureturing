---
slug: debski-barrycade-omitted-element-refutation
bibkey: debski2026barrycades
doi: 10.48550/arXiv.2609.18476
url: https://arxiv.org/abs/2609.18476v1
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.result
---

# Refutation of the printed barrycade omitted-element relation

## Problem

Michał Dębski, Jarosław Grytczuk, Paweł Naroski, Bartłomiej Pawlik,
Jakub Przybyło, and Małgorzata Śleszyńska-Nowak, *Finite and infinite
barrycades*, arXiv:2609.18476v1, Section 3.1, Conjecture 2 (2), print:

> A2(i) = A1(i) + 1 for every i >= 3.

The paper defines `A1(i)` as the least positive integer omitted from the
quasi-permutation `rho_i` and `A2(i)` as its first entry `rho_i(1)`.

## Motivation

Issue #8675 records the source quotation, its full universal scope, the
literature-status search, and the proposed `i = 3` counterexample. The result
tests the printed lower endpoint rather than a corrected statement beginning
at `i = 4`.

## Gap

The printed row `rho_3 = (4, 3, 1, 5, 6, ...)` omits 2 and begins with 4.
Consequently `A1(3) = 2` and `A2(3) = 4`, whereas the printed relation requires
`A2(3) = 3`. The bounded source and literature searches found no earlier
proof or refutation in the searched scope. This dossier makes no claim of
exhaustive literature coverage or publication priority.

## Route

Formalize the paper's partial-sum sets and greedy row recurrence with
zero-based indices, so Lean's `row 2` is the paper's `rho_3`. Strong induction
gives the first two rows in closed form. Least-element arguments for the third
row give `row 2 0 = 4`, `row 2 1 = 3`, and `row 2 2 = 1`, while the tail formula
shows that every positive integer other than 2 occurs in that row. Thus 2 is
its least omitted positive integer, but its first entry is 4. Instantiating the
printed universal statement at `i = 3` yields the contradiction `4 = 3`.

## Falsifier

A faithful proof that `rho_3` has a different first entry, contains 2, omits a
positive integer smaller than 2, or does not follow the formalized greedy
recurrence would invalidate this counterexample.

## Evidence

- Frozen result: `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.result`.
- The result has type `Not claim` and is kernel-checked in the pinned Lean
  toolchain.
- The proof derives `row 2 0 = 4`, `row 2 1 = 3`, `row 2 2 = 1`, and the
  third-row tail formula on the live path to the contradiction.

## Triage

`theorem`; resolution `refuted` for the literal lower endpoint in Conjecture 2
(2). The proof shape is `content`; the four form-(1) escape witnesses are
`row_zero`, `row_one`, `row_two_tail`, and `row_two_base`. Admission is by the
preregistered external-open-problem resolution in issue #8675.

## ASSUMED-UNVERIFIED

The bounded literature search is not exhaustive and does not establish
worldwide novelty or priority. Unpublished resolutions remain unverified.
