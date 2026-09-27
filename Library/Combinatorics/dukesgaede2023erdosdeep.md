---
bibkey: dukesgaede2023erdosdeep
authors: Peter J. Dukes, Tao Gaede
year: 2023
title: "Families of Modular Arithmetic Progressions with an Interval of Distance Multiplicities"
doi: 10.48550/arXiv.2208.05527
url: https://math.colgate.edu/~integers/x25/x25.pdf
claim: "Conjecture 1 proposes that the length triples of Erdos-deep families of three modular arithmetic progressions are exactly two infinite families and thirteen sporadic triples."
strata_touched:
  - D5/S3/Combinatorics/ErdosDeepTripleClassificationRefutation
license: citation-only
triage: anchor
---

# Dukes--Gaede modular arithmetic progressions with an interval of distance multiplicities

## Verified locator

URL: https://math.colgate.edu/~integers/x25/x25.pdf

DOI: 10.48550/arXiv.2208.05527

Version: *INTEGERS* **23** (2023), Article #A25, by Peter J. Dukes and Tao Gaede.
The arXiv record 2208.05527 carries only v1 (10 August 2022) and lists no later
version. The same conjecture appears as Conjecture 4.5 of Tao Gaede's University
of Victoria master's thesis *Erdős-Deep Families of Arithmetic Progressions*,
which states that its Chapters 3 and 4 are the basis of this article; the thesis
version carries one hypothesis the article does not display, recorded below.

## Definitions

Section 1 works in `Z_n` with `|x|_n := min(x, −x)`, each of `±x` reduced in
`{0, …, n−1}`, and sets `dist(x, y) = |x − y|_n`. For a family
`F = {A_1, …, A_s}` of subsets, `ΔF` is the multiset of the distances
`dist(x, y)` over pairs `{x, y} ⊆ A_i`, `x ≠ y`, for each `i`. The article defines

> we say that `F` is Erdős-deep if the multiplicities of distances that occur in
> `ΔF` are precisely `1, 2, …, k − 1` for some integer `k`.

Here `k` is determined by `k(k−1) = Σ_i k_i(k_i−1)` where `k_i = |A_i|`. It also
sets `AP_n(g, k) := {0, g, 2g, …, (k−1)g} ⊂ Z_n`, the modular `k`-term AP.
Theorem 2, the classification for `s = 2`, fixes the conventions carried over to
families of three: `k_1 ≥ k_2 ≥ 3` and `gcd(n, g_1, g_2) = 1`. Two members of a
family may coincide: the article's own `(6, 3, 3)` witness is
`{{0,1,2,3,4,5}, {0,4,8}, {0,4,8}}`.

## The statement in question

Section 5 states:

> Conjecture 1. An Erdős-deep family of three APs of lengths `k1 ≥ k2 ≥ k3` in
> `Z_n` exists if and only if `(k1, k2, k3) ∈ {(4, 4, 3), (6, 3, 3)}`, each for
> infinitely many n, or `(k1, k2, k3) ∈ {(6, 5, 3), (6, 6, 4), (6, 6, 6),
> (7, 7, 3), (9, 4, 3), (8, 7, 4), (8, 8, 5), (10, 6, 4), (12, 4, 4), (13, 5, 3),
> (13, 7, 4), (16, 5, 4), (21, 6, 4)}`, each for a finite number of values of n.

Conjecture 4.5 of the thesis is the same statement written in the tuple form
`(k, k1, k2, k3)`, with the extra hypothesis
`3 ≤ k3 ≤ k2 ≤ k1 ≤ ⌊n / (2·gcd(n, g1))⌋ + 1`. The thesis also prints the search
that produced the list: `k ∈ [4, 28]`; `g1, g2, g3 ≤ ⌊n/2⌋`;
`3 ≤ k3 ≤ k2 ≤ k1 ≤ ⌊n/(2·gcd(n,g1))⌋`; `n ∈ [2k1, 60]`; and, when
`gcd(g1, n) = 1`, only `g1 = 1` is checked, which is a valid reduction because
scaling every generator by a unit permutes the distances.

## Scope of the recorded answer

The conjecture is false, in both forms. In `Z_27` take

    A₁ = AP₂₇(1, 12) = {0,1,2,3,4,5,6,7,8,9,10,11}
    A₂ = AP₂₇(12, 6) = {0, 12, 24, 9, 21, 6}
    A₃ = AP₂₇(7, 5)  = {0, 7, 14, 21, 1}

with

    ΔA₁ = {1:11, 2:10, 3:9, 4:8, 5:7, 6:6, 7:5, 8:4, 9:3, 10:2, 11:1}
    ΔA₂ = {3:4, 6:3, 9:3, 12:5}
    ΔA₃ = {1:1, 6:2, 7:4, 13:3}
    ΔF  = {1:12, 2:10, 3:13, 4:8, 5:7, 6:11, 7:9, 8:4, 9:6, 10:2, 11:1, 12:5, 13:3}.

Thirteen distances occur, with multiplicities `1` through `13` each exactly once,
so `F` is Erdős-deep with `k = 14`, and `14·13 = 182 = 12·11 + 6·5 + 5·4`. The
conventions hold: `3 ≤ 5 ≤ 6 ≤ 12`, `gcd(27, 1, 12, 7) = 1`, and
`k₁ = 12 ≤ ⌊27/(2·1)⌋ + 1 = 14`. But `(12, 6, 5)` is neither of the two infinite
families nor one of the thirteen sporadic triples.

The witness lies inside the search the thesis describes: `n = 27 ≤ 60`,
`g₁ = 1`, `k₁ = 12 ≤ ⌊27/2⌋ = 13`, and `k = 14 ∈ [4, 28]`.

## Further witnesses and a scope note

Searching `n ≤ 84` and `k ≤ 28` under the article's conventions reproduces all
fifteen of its triples and yields twenty-seven in total. Eleven of the twelve
extra triples also satisfy the thesis bound on `k₁`:
`(9,9,4), (10,9,5), (10,10,6), (11,10,9), (11,11,5), (12,6,5), (12,9,3),
(12,11,6), (18,6,3), (20,5,5), (25,6,5)`. A second witness that can be checked by
hand is `n = 50`, `(20,5,5)`, `g = (1,10,10)`: there `A₁ = {0,…,19}` gives each
distance `d ≤ 19` multiplicity `20 − d`, while `A₂ = A₃ = {0,10,20,30,40}` each
give `10` five times and `20` five times, so the multiplicities are `1` through
`20`.

Separately, the article says the geometric infinite family
`F = {{0,1,2,3}, {0,3,6,9}, {0,1,2}}` is realised for `n ≥ 15`. At `n = 15` the
distance `9` folds to `|9|₁₅ = 6` and merges with the existing `6`s, giving
multiplicity three twice, so the family is Erdős-deep only for `n ≥ 16`. This
does not bear on Conjecture 1, which claims only that the triple occurs for
infinitely many `n`.

## Bounded prior-resolution evidence

The journal article, the arXiv record 2208.05527 (v1 only, no later version) and
the full text of Gaede's thesis were opened. The thesis presents the statement as
a conjecture and records no refutation; no later paper by either author on the
topic was found. Citation-index result pages were not reachable, so this is a
bounded negative finding and no worldwide priority claim is made.
