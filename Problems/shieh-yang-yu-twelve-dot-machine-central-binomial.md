---
slug: shieh-yang-yu-twelve-dot-machine-central-binomial
bibkey: yangshiehyu2025dotted
doi: null
url: https://arxiv.org/abs/2411.11914v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDot.result
---

# The 12̇-Machine Sorts a Central Binomial Number of Permutations

## Problem

Michael Yang, Hansen Shieh and Ashley Yu, *Stack-Sorting with Dotted-Pattern-Avoiding Stacks*, arXiv:2411.11914v2,
Section 6, Conjecture 6.1 (printed page 10):

> The machine-sortable permutations under the 12̇-machine map in Sₙ are enumerated by (2n−2 choose n−1).

The 12̇-machine is s ∘ s₁₂̇, with s West's stack-sorting map. By the source's Proposition 3.1, s₁₂̇ reverses each
peak run, a peak run being a maximal block of consecutive entries that starts at a left-to-right maximum. A
permutation is machine-sortable when the machine maps it to the identity.

## Motivation

The theorem `D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDot.result` establishes the statement: for every n ≥ 1, exactly
(2n − 2 choose n − 1) permutations of [n] are machine-sortable.

## Gap

Pre-registration issue 12225 records the literature screen: no work citing arXiv:2411.11914 treats this
conjecture, and GitHub searches for the identifier returned no hit outside this repository. This is a bounded
negative finding.

## Route

1. West's criterion is proved from the stack algorithm: s(w) is increasing exactly when w avoids 231.
2. Every image of the peak-run reversal ends in n, and the preimages of σn correspond to the subsets of the
   record positions of σ; so the count is the sum of 2^{rec(σ)} over 231-avoiding permutations σ of [n − 1].
3. A recursive bijection with Dyck paths, through the last primitive excursion, carries records to
   excursions.
4. Coloring each excursion by a bit and reflecting the marked excursions gives the balanced ±1 bridges of
   length 2(n − 1), which are counted by (2n − 2 choose n − 1).

## Falsifier

The statement would fail if West's criterion or the fibre description missed a sortable permutation, or if the
excursion decomposition or the reflection were not invertible.

## Evidence

Every structural lemma, the fibre bijection and both inverse identities were checked exhaustively on all
permutations of length at most 11; the counts agree with (2n − 2 choose n − 1) through n = 11.

## Triage

`theorem`; the statement is Conjecture 6.1 of arXiv:2411.11914 and is quantified over every n ≥ 1.

- Proved (formalized): the count of machine-sortable permutations of [n] equals the sum of 2^{rec(σ)} over
  231-avoiders σ of [n − 1], and equals (2n − 2 choose n − 1).
- Literature: the identity "Dyck paths of semilength m weighted by 2 to the number of returns sum to
  (2m choose m)" is classical; the new content is the fibre description of the 12̇-machine, which reduces the
  conjecture to it.
- Open: the source's companion questions for other dotted patterns beyond 12̇ and 21̇, and the distribution of
  the number of machine passes needed to sort.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation index, arXiv and GitHub searches and the repository checks
recorded above.
