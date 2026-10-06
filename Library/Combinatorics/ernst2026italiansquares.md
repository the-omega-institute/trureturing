---
bibkey: ernst2026italiansquares
authors: A. Ernst, S. Lia, C. O'Brien, J. Sheekey, J. Zumbrägel
year: 2026
title: "Generalising Latin square orthogonality and Frobenius-König with alternating sign matrices"
doi: 10.48550/arXiv.2606.25884
url: https://arxiv.org/abs/2606.25884v1
claim: "Section 8, Problem 8.3 asks which signed row and column margins are realizable in W_n."
strata_touched:
  - D5/S3/Combinatorics/Latin/AlternatingSignMargins
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Combinatorics/ernst2026italiansquares -->

# Alternating signed matrices and their margins

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2606.25884.
Primary version: https://arxiv.org/abs/2606.25884v1, Section 4, pp. 12–13,
and Section 8, p. 27, Problem 8.3.

## Source statement

Section 8, p. 27: “Section 4 introduces the set W_n consisting of all
(0, ±1)-matrices in which the non-zero entries of each row and column
alternate in sign, and the sum of each row/column is in {0, ±1}.”

Section 8, p. 27: “Problem 8.3. For which (0, ±1)-vectors R and S of order n
does there exist X ∈ W_n with row-sums R and column-sums S?”

## Encoding and scope

Entries and sums are integers. Rows and columns use the natural order on
`Fin n`. Alternation compares consecutive nonzero entries, allowing either
first sign and either last sign. Zero lines are allowed. The empty order is
included in the formal statement. The source asks for a characterization;
equality of the two total sums is the answer proved in
`D5/S3/Combinatorics/Latin/AlternatingSignMargins.result`, rather than a
result attributed to the paper. The source's prescribed zero-pattern and
border-sign questions are outside that theorem.
