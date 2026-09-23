---
slug: erdos-deep-triple-classification-refutation
bibkey: dukesgaede2023erdosdeep
doi: 10.48550/arXiv.2208.05527
url: https://math.colgate.edu/~integers/x25/x25.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.result
---

# Erdos Deep Triple Classification Refutation

## Problem

Dukes and Gaede, *INTEGERS* 23 (2023), Article #A25, work in `Z_n` with
`|x|_n := min(x, −x)` and `dist(x, y) = |x − y|_n`. For a family
`F = {A_1, …, A_s}`, `ΔF` is the multiset of distances `dist(x, y)` over pairs
`{x, y} ⊆ A_i`, and `F` is Erdős-deep when "the multiplicities of distances that
occur in `ΔF` are precisely `1, 2, …, k − 1` for some integer `k`". They write
`AP_n(g, k) := {0, g, 2g, …, (k−1)g}`, and Theorem 2 fixes the conventions for
families of APs: lengths at least three and `gcd(n, g_1, …, g_s) = 1`. Section 5
states:

> Conjecture 1. An Erdős-deep family of three APs of lengths `k1 ≥ k2 ≥ k3` in
> `Z_n` exists if and only if `(k1, k2, k3) ∈ {(4, 4, 3), (6, 3, 3)}`, each for
> infinitely many n, or `(k1, k2, k3) ∈ {(6, 5, 3), (6, 6, 4), (6, 6, 6),
> (7, 7, 3), (9, 4, 3), (8, 7, 4), (8, 8, 5), (10, 6, 4), (12, 4, 4), (13, 5, 3),
> (13, 7, 4), (16, 5, 4), (21, 6, 4)}`, each for a finite number of values of n.

Conjecture 4.5 of Gaede's University of Victoria thesis states the same with one
further hypothesis, `3 ≤ k3 ≤ k2 ≤ k1 ≤ ⌊n / (2·gcd(n, g1))⌋ + 1`.

## Motivation

The frozen theorem
`D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation.result` refutes the
stronger of the two forms, hence both. The classification of Erdős-deep triples
therefore remains open, and the list published for it is incomplete rather than
merely unproved.

## Gap

The journal article, the arXiv record 2208.05527 (v1 only, no later version) and
the full text of Gaede's thesis were opened. The thesis presents the statement as
a conjecture and records no refutation; no later work by either author on the
topic was found. Citation-index result pages were not reachable, so this is a
bounded negative finding.

## Route

In `Z_27` take the three progressions

    A₁ = AP₂₇(1, 12) = {0,1,2,3,4,5,6,7,8,9,10,11}
    A₂ = AP₂₇(12, 6) = {0, 12, 24, 9, 21, 6}
    A₃ = AP₂₇(7, 5)  = {0, 7, 14, 21, 1}.

Their distance multisets are

    ΔA₁ = {1:11, 2:10, 3:9, 4:8, 5:7, 6:6, 7:5, 8:4, 9:3, 10:2, 11:1}
    ΔA₂ = {3:4, 6:3, 9:3, 12:5}
    ΔA₃ = {1:1, 6:2, 7:4, 13:3}

with 66, 15 and 10 pairs respectively, so

    ΔF = {1:12, 2:10, 3:13, 4:8, 5:7, 6:11, 7:9, 8:4, 9:6, 10:2, 11:1, 12:5, 13:3}.

Thirteen distances occur and their multiplicities are `1` through `13`, each
exactly once, so `F` is Erdős-deep with `k = 14`, matching
`14·13 = 182 = 12·11 + 6·5 + 5·4`. Every convention holds: `3 ≤ 5 ≤ 6 ≤ 12`,
`gcd(27, 1, 12, 7) = 1`, and `k₁ = 12 ≤ ⌊27/(2·1)⌋ + 1 = 14`. The triple
`(12, 6, 5)` is neither of the two infinite families nor one of the thirteen
sporadic triples, so the conjectured classification fails.

## Falsifier

A single distance recomputed differently would break the witness. The two
independent checks are the pair count, `66 + 15 + 10 = 91 = 13·14/2`, and the
requirement that each multiplicity from one to thirteen occurs exactly once; both
are visible in the table above. Widening the length conventions produces spurious
counterexamples and must be avoided: admitting progressions of length two yields
triples such as `(11, 5, 2)`, which the source's conventions exclude.

## Evidence

An independent search under the source's conventions over `n ≤ 84` and `k ≤ 28`
reproduces all fifteen of its triples and returns twenty-seven in total. Eleven
of the twelve extra triples also satisfy the thesis bound on `k₁`:
`(9,9,4), (10,9,5), (10,10,6), (11,10,9), (11,11,5), (12,6,5), (12,9,3),
(12,11,6), (18,6,3), (20,5,5), (25,6,5)`. Nine witnesses were cross-checked
against a second, independent implementation, and the two used here were verified
by hand. The second hand-checkable witness is `n = 50`, `(20,5,5)`,
`g = (1,10,10)`: `A₁ = {0,…,19}` gives distance `d` multiplicity `20 − d`, and
`A₂ = A₃ = {0,10,20,30,40}` each give `10` five times and `20` five times, so the
multiplicities are `1` through `20`.

The witness lies inside the search the thesis prints: `k ∈ [4, 28]`,
`g₁, g₂, g₃ ≤ ⌊n/2⌋`, `3 ≤ k₃ ≤ k₂ ≤ k₁ ≤ ⌊n/(2·gcd(n,g₁))⌋`, `n ∈ [2k₁, 60]`,
and `g₁ = 1` whenever `gcd(g₁, n) = 1`. Here `n = 27 ≤ 60`, `g₁ = 1`,
`k₁ = 12 ≤ ⌊27/2⌋ = 13` and `k = 14 ∈ [4, 28]`, so the triple was within the
stated range.

## Triage

`theorem`; Tier 1 named external open problem, preregistered in issue 9317 before
implementation. The admission basis is `open-problem-resolution`. The
classification is `proof_shape: content`; the escape content is that the three
progressions named above realise the multiplicities one through thirteen exactly
once each, which is not an instantiation, projection or normalisation of a pinned
upstream statement. The computational use is a `certified-instance` with a typed
`refutes` edge from `result` to `claim`.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the journal article, the sole arXiv version and
Gaede's thesis were opened; citation-index result pages were not reachable, so no
worldwide priority claim is made.

The classification itself is not supplied here. The eleven extra triples listed
above are what one search over `n ≤ 84` and `k ≤ 28` returns; nothing is claimed
about triples outside that range, about which of them occur for infinitely many
`n`, or about the correct form of the conjecture.

Separately, the article states that the geometric infinite family
`{{0,1,2,3}, {0,3,6,9}, {0,1,2}}` is realised for `n ≥ 15`. At `n = 15` the
distance `9` folds to `|9|₁₅ = 6`, giving multiplicity three twice, so that
family is Erdős-deep only for `n ≥ 16`. This does not bear on Conjecture 1, which
claims only that the triple occurs for infinitely many `n`.
