---
bibkey: franklin2024inversions
authors: Atli Fannar Franklín
year: 2024
title: "Pattern avoiding permutations enumerated by inversions"
doi: 10.48550/arXiv.2410.07467
url: https://arxiv.org/abs/2410.07467v4
claim: "Section 1 conjectures on indecomposable pattern-avoiding permutations counted by inversions, including the count of I_k(321, 1342)."
strata_touched:
  - D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion
license: citation-only
triage: anchor
---

# Franklín, pattern avoiding permutations enumerated by inversions

The paper counts pattern-avoiding permutations by their number of inversions. Its central objects are the sets
I_k of direct-sum indecomposable permutations, of any length, with exactly k inversions; an indecomposable
permutation of length n has at least n − 1 inversions, so each I_k is finite.

Section 1, printed pages 2–3, states two conjectures. The first identifies I_k(132, 4321) with partitions having
no part strictly between the smallest and the largest part; it is proved in Claesson, Linusson, Ulfarsson and
Verkama, arXiv:2604.01143v1, Section 7.6, Proposition 7.7. The second reads:

> Another case is I_k(321, 1342), which we conjecture to have k(k + 1)/2 + 1 elements.

The printed formula fails at k = 1, where I_1 = {21}. The counts 1, 1, 2, 4, 7, 11, 16, 22, 29 for k = 0, …, 8
equal k(k − 1)/2 + 1; the printed formula equals the count of I_{k+1}(321, 1342). The module
`D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion` proves |I_k(321, 1342)| = k(k − 1)/2 + 1 for every
k and refutes the printed formula.

The journal version appeared in Discrete Mathematics & Theoretical Computer Science 27:1, Permutation Patterns
2024 (special issue, 2025); its text was not compared with arXiv v4.

## Verified locator

DOI: 10.48550/arXiv.2410.07467

URL: https://arxiv.org/abs/2410.07467v4

- Locator: Section 1, printed pages 2–3, conjecture on I_k(321, 1342).
- Locator: Section 1, printed page 2, conjecture on I_k(132, 4321).
- Locator: Section 1, definition of I_k as the indecomposable permutations with exactly k inversions.
