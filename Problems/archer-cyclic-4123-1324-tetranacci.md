---
slug: archer-cyclic-4123-1324-tetranacci
bibkey: archer2024pattern
doi: 10.48550/arXiv.2408.15000
url: https://arxiv.org/abs/2408.15000v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ArcherCyclicTetranacci.result
---

# Cyclic Permutations Avoiding 4123 with 1324-Avoiding Cycle Forms

## Problem

Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves and Millie Jeske, *Pattern-restricted
cyclic permutations with a pattern-restricted cycle form*, arXiv:2408.15000v1, Section 4:

> we conjecture that |A°_n(4123;1324)| is the (n−2)nd Tetranacci number

Here `A°_n(4123; 1324)` is the set of cyclic permutations of `1, …, n` whose one-line notation avoids
`4123` and all of whose cycle forms, the rotations of the cycle word, avoid `1324`.

## Motivation

Let `T_0 = T_1 = T_2 = 0`, `T_3 = 1` and `T_{k+4} = T_{k+3} + T_{k+2} + T_{k+1} + T_k` (OEIS A000078).
The theorem `D5/S3/Combinatorics/ArcherCyclicTetranacci.result` establishes
`|A°_n(4123; 1324)| = T_{n+2}` for every `n ≥ 1`; the counts for `n = 1, …, 9` are
`1, 1, 2, 4, 8, 15, 29, 56, 108`.

## Gap

Pre-registration issue 11214 records the literature screen. Of the three papers citing
arXiv:2408.15000, Pan's arXiv:2409.17482 proves only the Pell case `(2431; 1324)` and Pan's
arXiv:2505.02045 settles conjectures of the earlier paper arXiv:2312.05145 on the standard cycle form.
The repository had no result for this class. These are bounded negative findings.

## Route

1. Encode a cyclic permutation by its cycle word rooted at `1`. Four entries give a `1324` in some
   rotation exactly when their circular order can be read as `x, y, z, t` with `x < z < y < t`; hence
   the part of a valid cycle word after `1` avoids `213`.
2. If `2` does not follow `1` directly, write the word as `1, P, 2, S`. Every entry of `P` exceeds
   every entry of `S`, `S` is increasing, `P` begins with the smallest entry above `S`, and one-line
   `4123`-avoidance forces `|S| ≤ 2`.
3. The maps that insert a new entry after `1`, or a block `2, 3, …, k` with `k = 2, 3, 4`, preserve both
   conditions in both directions, and every valid word arises from exactly one of them.
4. The resulting recurrence `a_n = a_{n−1} + a_{n−2} + a_{n−3} + a_{n−4}` with `a_1 = a_2 = 1, a_3 = 2,
   a_4 = 4` matches `T_{n+2}`.

## Falsifier

The statement would fail if some `n` had a count different from `T_{n+2}`. It depends on reading
"all cycle forms" as every rotation of the cycle word; requiring only the standard cycle form to avoid
`1324` gives a different class.

## Evidence

Exhaustive enumeration of all cycle words through `n = 10` agrees with every structural lemma and with
the counts `1, 1, 2, 4, 8, 15, 29, 56, 108, 208`.

## Triage

`theorem`; the conjecture is stated in the Open Questions of arXiv:2408.15000v1 and is quantified over
every `n`.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, arXiv searches and repository checks recorded
above.
