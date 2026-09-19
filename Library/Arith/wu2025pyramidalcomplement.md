---
bibkey: wu2025pyramidalcomplement
authors: Chai Wah Wu
year: 2025
title: Algorithms for Complementary Sequences
doi: 10.5281/zenodo.17535229
url: https://math.colgate.edu/~integers/z95/z95.pdf
claim: "Conjecture 1. For k >= 9, (6) holds for all n >= 1."
strata_touched:
  - D5/S3/Arith/WuPyramidalComplement
license: citation-only
triage: anchor
---

# Algorithms for Complementary Sequences

Wu defines the complementary sequence as the increasing sequence of positive
integers absent from a prescribed increasing sequence. On printed page 2 this
is the `n`-th positive integer outside the source image, so the index is
one-based and zero is not a complement term.

For the k-gonal-pyramidal sequence, printed page 11 gives Equation (6). With

```text
h = floor((6n/(k-2))^(1/3)),
U = (k-2)h^3 + 3(k-1)h^2 + (2k-1)h + 6,
L = h(h-1)(h(k-2)+k+1),
```

the proposed term is `n+h+1` when `6n >= U`, `n+h-1` when the first branch
fails and `6n <= L`, and `n+h` otherwise. Printed page 12 states Conjecture 1:

> For k >= 9, (6) holds for all n >= 1.

The earlier results in the article prove formulas for other parameter ranges
or for sufficiently large indices; they do not prove this all-index statement.

The checked source is the 26-page INTEGERS 25 (2025), article A95 PDF. Its
SHA-256 is
`b4c7db146554cb2b4e88901ab4fd3799a41f46797b9b9d4e851f39aca60c690b`.

## Verified locator

- DOI: https://doi.org/10.5281/zenodo.17535229
- URL: https://math.colgate.edu/~integers/z95/z95.pdf
- Exact source locations: complementary-sequence definition on printed page 2; Equation (6) on printed page 11; Conjecture 1 on printed page 12.

## Literature boundary

The arXiv record `2409.05844` through version 10, the journal version, Wu's
publication list including its 2026 entries, and the author's public sequence
repository were checked within the stated bounded search. GitHub code searches
for `2409.05844` and `complementary sequences` returned zero complete hits;
the two `pyramidal` hits were a partial sequence definition and a formula
registry, not this theorem. DataCite returned no indexed citations for the
arXiv or journal record. Later-title searches returned papers about signal or
Golay complementary sequences, not this number-theoretic conjecture.

OpenAlex and Semantic Scholar returned HTTP 429, so their citation graphs were
not verified. The search is not exhaustive and establishes neither worldwide
novelty nor priority. An earlier complete published resolution would supersede
the open-problem assessment without affecting the formal theorem's kernel
validity.

## Repository settlement

The repository proves the full source statement for every `k >= 9` and
`n >= 1` as
`D5/S3/Arith/WuPyramidalComplement.wu_conjecture_one`. The theorem's frozen
`sourceStatementId` is
`sha256:7b0c4f46be19f41459abfe30393dba3916c440231d0e079d0e55b3cd949dcf89`;
its containing module is frozen at
`sha256:627b09b5bbcd81cb4f97b0496c330457ceb734fb6810d90291ff360ba64cb6d7`.
This formal settlement does not strengthen the bounded novelty or priority
claim above.
