---
slug: ta-2025-problem-11-6-three-invariant-refutation
bibkey: ta2025goodinvolutions
doi: 10.48550/arXiv.2505.08090
url: https://arxiv.org/abs/2505.08090v5
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.result
---

# Ta Problem 11.6: three invariants do not determine the count

## Problem

Lực Ta, *Good involutions of conjugation subquandles*, arXiv:2505.08090v5,
Section 11, Problem 11.6, asks:

> Let G be a finite nonabelian group of order n. Is the number of good
> involutions of Conj G completely determined by n, the order of the
> center Z(G), and the class number k(G) of G? If so, is there an exact
> formula to compute this number?

Here `s_x(y)=xyx^-1`. A good involution is a function rho with rho squared
equal to the identity, commuting with every s_x, and satisfying
`s_(rho(x))=s_x^-1`. The count is of all such functions on the whole group,
without quotienting by quandle isomorphism. This is separate from 11.7's
question about a bound for conjugation subquandles.

## Motivation

The requested determination would force any two finite nonabelian groups
with identical `(order, center order, class number)` to have identical good-map
counts. The formal `claim : Prop` states exactly that pairwise assertion.
Its negation also excludes any formula depending only on those three numbers.
The original question and the proposed complete counterexample were registered
in [issue #25997](https://github.com/the-omega-institute/trureturing/issues/25997)
before this native implementation.

## Gap

The primary v5 text still poses 11.6. The inspected versioned texts
2608.19951v1 and 2508.16772v1 did not identify a prior answer to 11.6.
Nakajima–Yamaguchi, 2608.19951v1, Example 6.8 and the following paragraph,
instead refute Ta's 11.8 and 11.9. This is a bounded literature check on
2026-11-03, not exhaustive citation coverage, worldwide priority, or uniqueness.
The existing repository 11.7 refutation does not settle this question.

## Route

Take native Mathlib semidirect products `G_r=(Z/16) ⋊_r (Z/4)`, for r=5 and
r=7, with multiplication `(i,j)(k,l)=(i+r^j k,j+l)`. Both are nonabelian
groups with invariant triple `(64,4,22)`.

The central-label characterization is attributed to Ta Theorem 6.7. Our
label `z(x)=rho(x)x` is the inverse of the source's zeta. Good maps correspond
bijectively to class-invariant central labels satisfying
`z(z(x)x^-1)=z(x)`. A complete conjugacy partition and a complete enumeration
of the actual center split this compatibility into independent blocks.

For r=5 the local factors are one 10, six 4s, and three 6s; hence the complete
count is `10*4^6*6^3=8847360`. For r=7 they are four 10s and three 6s;
hence the count is `10^4*6^3=2160000`. Each local block has at most four
classes and four central labels. The local enumeration has at most `4^4`
assignments, and the general bijection proves completeness for all maps;
there is no enumeration of `64^64` functions or `4^22` global assignments.

## Falsifier

The refutation would fail if either action did not define the native group,
either group were abelian, any of the three invariants differed, the
classifier omitted or conflated conjugacy classes, the center enumeration
omitted central elements, the destination tables disagreed with native group
operations, or the local counts did not count every compatible assignment.
Those obligations occur on the live path to the full Lean result.

## Evidence

The mathematical source is
`D5/S3/FiniteGroups/Quandles/TaThreeInvariantRefutation.lean` with literal
`claim : Prop` and `result : Not claim`. The two complete counts are the
conjunction `good_counts`, consumed by `result`. General classification and
factorization live in `D5/S3/FiniteGroups/Quandles/CentralLabels.lean` and
`BlockCounting.lean`, and the counts use the existing whole-carrier Good
interface from `D5/S3/FiniteGroups/Quandles/ConjugationSubquandle.lean`,
shared with the repository's 11.7 refutation.

This dossier does not certify independent review, admission, frozen status,
required CI, merge, official acceptance, priority, or a solved-problem KPI.
Those are distinct delivery obligations.

## Triage

`theorem`; the designated resolution is `refuted` for the original
three-invariant determination assertion. The two concrete groups, all three
invariants, and both complete counts are required together. No claim about
knot classification, all finite groups' counts, or counts modulo isomorphism
is substituted for the original.

The mechanism explains the failure: the three invariant cardinalities do
not specify how central twisted inversion links the conjugacy classes.
The general block certificate retains that extra structure and yields a
complete product formula. The central-label characterization itself is
source-attributed, not claimed as new priority.

## ASSUMED-UNVERIFIED

Source faithfulness remains an independent mathematical review judgment.
The literature check is bounded as described above. Escape registration of
the new public counting theorems remains unfinished under issue #25997:
the full dependent group/partition/center telescope still needs a faithful
realization bridge and variation, sensitivity and actual observational
dependence proofs. No `declared_validated` registration is asserted.
