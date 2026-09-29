---
slug: archer-cyclic-4132-1324-padovan
bibkey: archer2024pattern
doi: 10.48550/arXiv.2408.15000
url: https://arxiv.org/abs/2408.15000v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ArcherCyclicPadovan.result
---

# Cyclic Permutations Avoiding 4132 with 1324-Avoiding Cycle Forms

## Problem

Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves and Millie Jeske, *Pattern-restricted
cyclic permutations with a pattern-restricted cycle form*, arXiv:2408.15000v1, Section 4:

> we conjecture that … |A°_n(4132;1324)| is the (3n)th Padovan number

Here `A°_n(4132; 1324)` is the set of cyclic permutations of `1, …, n` whose one-line notation avoids
`4132` and all of whose cycle forms, the rotations of the cycle word, avoid `1324`.

## Motivation

Let `P_0 = 1`, `P_1 = P_2 = 0` and `P_{k+3} = P_{k+1} + P_k` (OEIS A000931). The theorem
`D5/S3/Combinatorics/ArcherCyclicPadovan.result` establishes `|A°_n(4132; 1324)| = P_{3n}` for every
`n ≥ 1`; the counts for `n = 1, …, 9` are `1, 1, 2, 5, 12, 28, 65, 151, 351`. Equivalently, their
generating function is `x(1 − x)² / (1 − 3x + 2x² − x³)`.

## Gap

Pre-registration issue 11215 records the literature screen. Of the three papers citing
arXiv:2408.15000, Pan's arXiv:2409.17482 proves only the Pell case `(2431; 1324)` and Pan's
arXiv:2505.02045 settles conjectures of the earlier paper arXiv:2312.05145 on the standard cycle form.
The repository had no result for this class. These are bounded negative findings.

## Route

1. Encode a cyclic permutation by its cycle word rooted at `1`. A selected quadruple is a `1324` in
   some rotation exactly when the three entries read cyclically after its minimum form a `213`.
2. Write a valid cycle word as `1, L, 2, R`. If `L` is empty, deleting `2` gives a valid word of length
   `n − 1`. Otherwise every entry of `L` exceeds every entry of `R`, `R` is increasing, and `1, L`
   standardizes to a valid word.
3. In that block form the one-line word avoids `4132` exactly when its tail avoids `4132` and the tail
   entries below the first entry of `L` increase. This defines an auxiliary class `D_k` with
   `d_k = b_k + d_{k−1}`, and `b_n = b_{n−1} + Σ_{k=1}^{n−2} d_k`.
4. Eliminating `d` gives `b_n = 3b_{n−1} − 2b_{n−2} + b_{n−3}` for `n ≥ 4`, the recurrence satisfied by
   `P_{3n}`, with matching initial values `1, 1, 2`.

## Falsifier

The statement would fail if some `n` had a count different from `P_{3n}`. It depends on reading
"all cycle forms" as every rotation of the cycle word and on the Padovan indexing of OEIS A000931.

## Evidence

Exhaustive enumeration of all cycle words through `n = 10` agrees with the decomposition, both one-line
criteria, the auxiliary split and the counts `1, 1, 2, 5, 12, 28, 65, 151, 351, 816`.

## Triage

`theorem`; the conjecture is stated in the Open Questions of arXiv:2408.15000v1 and is quantified over
every `n`.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, arXiv searches and repository checks recorded
above.
