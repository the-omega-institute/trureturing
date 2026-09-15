---
slug: vatter-largest-derangement-limit-below-one
bibkey: vatter2026assortment
doi: null
url: https://arxiv.org/abs/2602.16355
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/DerangementRatioNonconvergence
---

# Vatter's largest derangement limit below one

## Problem

Vincent Vatter, "An Assortment of Problems in Permutation Patterns:
Unimodality, Equivalence, Derangements, and Sorting", arXiv:2602.16355v2,
Section 4, unnumbered paragraph immediately after Question 4.3:

> Is there a largest possible limit strictly less than 1?

Locator: https://arxiv.org/html/2602.16355v2#S4. This dossier concerns only
that sentence. It is distinct from the universal convergence question and
has no problem number of its own.

A permutation class is a downset of actual permutations under subsequence
order-isomorphism. Write `C_n` for its length-`n` slice, `C_n°` for the
fixed-point-free members, and `r_C(n) = |C_n°| / |C_n|`. Let `Attained(l)`
mean that some such class has nonempty slices at every length and
`r_C(n) -> l` as `n -> infinity`. The affirmative largest-attained-limit
proposition is

```text
exists L in R, L < 1 and Attained(L) and
  forall l in R, (l < 1 and Attained(l)) implies l <= L.
```

The source imposes no growth or finite-basis condition. Nonempty slices are
provided by the constructed witnesses, so their ratios do not rely on an
empty-denominator convention. Even if a broader convention admits additional
limits, any proposed maximum `L < 1` is contradicted by the same witness
construction with `q = L`.

## Motivation

This is a first-tier question explicitly posed in a 2026 paper. The existing
`PermClass`, `Contains`, `IsDerangement`, and `ratio` carriers express its
objects. A family of attained limits cofinal below one decides maximality
without requiring a classification of every possible limit.

## Gap

The scoped source and literature searches recorded in
`Library/Words/vatter2026assortment.md` found no direct prior answer to this
single question. They do not certify global publication priority. The
separate Question 4.3 already has its own dossier and resolution; the known
Hoffman-Rizzolo-Slivken implications for Conjecture 4.1 and Question 4.2
supply no new answer here. The full set of attainable limits is outside this
result.

## Route

For each natural `k`, let `C_k` contain the genuine permutations
`P(n,a) = (a+1,...,n,a,...,1)` for `a <= min(k,n)`. Any contained pattern
is another two-block permutation whose decreasing tail is no longer than
the original tail. Thus `C_k` is hereditary. At every length it contains
`P(n,0)`, including the empty permutation at length zero.

For `n > 2*k+2`, the parameters `a=0,...,k` give exactly `k+1` distinct
members. The `a=0` member is the identity and has a fixed point; exactly
the `k` positive parameters give derangements. Consequently the ratio is
eventually `k/(k+1)`. These are symbolic statements for all `k` and all
lengths beyond the threshold, not a finite grid of observations.

For any real `q < 1`, choose a natural `k > q/(1-q)`. Then
`q < k/(k+1) < 1`, and eventual constancy proves convergence for `C_k`.
Given a putative largest attained limit `L < 1`, apply
`exists_derangement_limit_between` with `q=L`. Its larger attained limit
contradicts maximality. This is why the existing positive cofinality
theorem refutes the affirmative proposition; no separate negation theorem
is needed.

## Falsifier

A largest attained limit `L < 1` would contradict the endpoint instantiated
at `L`. A defect in the pattern-closure proof, the large-length parameter
bijection, or the fixed-point classification would invalidate the
construction. A source restriction excluding eventually constant slice sizes
would invalidate the claimed source scope; the inspected v2 text has no such
restriction. A prior direct published answer would defeat a priority claim
without changing the mathematical argument.

## Evidence

The substantive endpoint is
`D5/S1/Words/Patterns/DerangementLimitsCofinal.exists_derangement_limit_between`:

```text
forall q : R, q < 1 implies
  exists C : PermClass, exists l : R,
    q < l and l < 1 and
    (forall n, (C.mem n).Nonempty) and
    Tendsto (ratio C) atTop (nhds l).
```

Its live proof uses `pattern_tailPerm`, `boundedTailClass`, and
`boundedTailClass_counts`. The current canonical Lean report includes two
definitions and three theorems. All three theorems have exactly
`Classical.choice`, `Quot.sound`, and `propext` in their axiom closures.
The canonical build and report completed with exit 0 under Lean 4.33.0 and
Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`.

The supplied v2 source capture was checked against SHA-256
`fe961429a3cdedc8610d538b16850eca02b75a5bc0bca70a745f5339b71f25f6`.
Its class definition permits arbitrary downsets. The construction is
repository-derived; the source is cited for the question.

## Triage

`theorem`. Cofinality gives a negative answer to the literal largest-limit
question for arbitrary hereditary classes. The construction uses eventually
constant slice sizes and establishes no assertion about a variant requiring
growth. It does not classify all attainable limits.

## ASSUMED-UNVERIFIED

Publication priority outside the recorded search scope is ASSUMED-UNVERIFIED.
The source/citation and bounded-grid searches, GitHub discussion result, and
bounded third-party code-search results are supplied research evidence; they
were not independently repeated for this dossier. The source wording and
definitions were inspected in the supplied v2 capture, without a fresh web
fetch. Source-to-Lean fidelity and the maximality-to-cofinality interpretation
have independent semantic review, but are not facts certified by the Lean
kernel or by the resolution metadata validator.
