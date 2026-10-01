---
bibkey: benyi2024pattern
authors: Beáta Bényi, Toufik Mansour, José L. Ramírez
year: 2024
title: "Pattern Avoidance in Weak Ascent Sequences"
doi: 10.46298/dmtcs.12273
url: https://arxiv.org/abs/2309.06518v4
claim: "The sequence w_210(n) coincides with the sequence A117106."
strata_touched:
  - D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter
license: citation-only
triage: anchor
---

# Bényi, Mansour and Ramírez, pattern avoidance in weak ascent sequences

The paper enumerates weak ascent sequences avoiding a single pattern of length three for the patterns
001, 011, 012, 021 and 102, relates several of these classes to compositions, upper triangular 01-matrices
and plane trees, and leaves the remaining length-three patterns open, with one conjectured enumeration.

## Verified locator

DOI: 10.46298/dmtcs.12273

URL: https://arxiv.org/abs/2309.06518v4

- Locator: Section 1, a weak ascent sequence is a sequence e_1 ⋯ e_n of nonnegative integers with
  e_1 = 0 and e_i ≤ 1 + wasc(e_1 ⋯ e_{i−1}), where wasc counts the positions j with e_j ≤ e_{j+1};
  w_p(n) counts those of length n avoiding the pattern p.
- Locator: Section 3, Table 2 lists w_p(n) for p ∈ {000, 010, 100, 101, 110, 120, 201, 210}, whose
  enumeration is left open.
- Locator: Section 3, Conjecture 3.1: the sequence w_210(n) coincides with A117106, which enumerates
  permutations avoiding the vincular pattern 2-41-3.

## Reading of the statement

The numbers of 210-avoiding weak ascent sequences of length n = 0, …, 10 are 1, 1, 2, 6, 23, 104, 530,
2958, 17734, 112657, 750726; the same numbers count the permutations of [n] avoiding 2-41-3 (the
semi-Baxter numbers of Bouvel, Guerrini, Rechnitzer and Rinaldi).

## Bounded prior-resolution evidence

Read on 2026-10-01: the papers citing arXiv:2309.06518 that were located are Mansour, *Three Classes of
Pattern-Avoiding Weak Ascent Sequences* (Experimental Mathematics, 2026; patterns 0123, 0012, 0021),
Mansour, *Statistics in Weak Ascent Sequences* (Mathematics 14 (2026) 1378), Callan and Mansour on pairs
and triples of patterns (Discrete Mathematics 348 (2025) 114438), and Zhou on revised ascent sequences
(arXiv:2505.05171); none treats Conjecture 3.1. OEIS A117106 links the paper without recording a proof.
This is a bounded negative finding.
