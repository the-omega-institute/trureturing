---
bibkey: archer2024pattern
authors: Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske
year: 2024
title: "Pattern-restricted cyclic permutations with a pattern-restricted cycle form"
doi: 10.48550/arXiv.2408.15000
url: https://arxiv.org/abs/2408.15000v1
claim: "we conjecture that |A°_n(4123;1324)| is the (n−2)nd Tetranacci number, that |A°_n(2431;1324)| is the (n−1)st Pell number, and |A°_n(4132;1324)| is the (3n)th Padovan number."
strata_touched:
  - D5/S3/Combinatorics/ArcherCyclicTetranacci
  - D5/S3/Combinatorics/ArcherCyclicPadovan
license: citation-only
triage: anchor
---

# Archer, Borsh, Bridges, Graves and Jeske, cyclic permutations with a restricted cycle form

The paper studies cyclic permutations that avoid a pattern in one-line notation while every one of
their cycle forms avoids a second pattern, enumerates several such classes, and closes with conjectured
enumerations for three pattern pairs.

## Verified locator

DOI: 10.48550/arXiv.2408.15000

URL: https://arxiv.org/abs/2408.15000v1

- Locator: Section 1, `A°_n(σ; τ)` is the set of cyclic permutations of `[n]` whose one-line notation
  avoids `σ` and all of whose cycle forms avoid `τ`; a cyclic permutation has `n` cycle forms, the
  rotations of its cycle word.
- Locator: Section 4, Open Questions: "we conjecture that |A°_n(4123;1324)| is the (n−2)nd Tetranacci
  number, that |A°_n(2431;1324)| is the (n−1)st Pell number, and |A°_n(4132;1324)| is the (3n)th Padovan
  number."

## Reading of the statement

For `n = 1, 2, …` the three counts are `1, 1, 2, 4, 8, 15, 29, 56, 108, …` for `(4123; 1324)`,
`1, 1, 2, 5, 12, 29, 70, 169, 408, …` for `(2431; 1324)` and `1, 1, 2, 5, 12, 28, 65, 151, 351, …` for
`(4132; 1324)`: the Tetranacci numbers of OEIS A000078 at index `n + 2`, the Pell numbers, and the
Padovan numbers of OEIS A000931 at index `3n`.

## Bounded prior-resolution evidence

Read on 2026-09-29: the Semantic Scholar citation list of arXiv:2408.15000 has three entries. Pan,
arXiv:2409.17482, proves the Pell case `(2431; 1324)`. Pan, arXiv:2505.02045, settles two conjectures of
the earlier paper arXiv:2312.05145 about the standard cycle form. An arXiv search for cyclic permutations
with pattern-restricted cycle forms up to March 2026 found no treatment of `(4123; 1324)` or
`(4132; 1324)`. This is a bounded negative finding.
