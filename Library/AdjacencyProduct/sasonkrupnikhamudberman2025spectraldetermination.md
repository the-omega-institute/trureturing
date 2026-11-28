---
bibkey: sasonkrupnikhamudberman2025spectraldetermination
authors: Igal Sason; Noam Krupnik; Suleiman Hamud; Abraham Berman
year: 2025
title: On Spectral Graph Determination
doi: 10.3390/math13040549
url: https://arxiv.org/abs/2412.20775v6
claim: "Question 5.21 asks whether both closed-neighborhood corona pairs in Theorem 5.20 are normalized-Laplacian cospectral."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian
license: citation-only
triage: anchor
---

## Verified locator

[Journal DOI](https://doi.org/10.3390/math13040549) · [Version 6](https://arxiv.org/abs/2412.20775v6)

In arXiv:2412.20775v6, Theorem 5.20 uses a pair of regular adjacency-cospectral graphs and an arbitrary third graph. It considers the pair as the base factor and as the attached factor. Question 5.21 asks whether the same pairs are cospectral for the normalized Laplacian. [Theorem 5.20](https://arxiv.org/html/2412.20775v6#S5.Thmtheorem20) · [Question 5.21](https://arxiv.org/html/2412.20775v6#S5.Thmtheorem21)

The normalized Laplacian in equation (2.16) is the degree-scaled ordinary Laplacian. Inverse square-root degree is zero at an isolated vertex, which gives a zero row and column. [Equation (2.16)](https://arxiv.org/html/2412.20775v6#S2.E16)

## Formal correspondence

`ClosedNeighborhoodCorona.normalized_laplacian_charpoly_corona` proves equality of the two real characteristic polynomials in each factor order. The graph vertex types may be chosen independently. The two regularity premises have separate degree parameters, and the third graph has no regularity premise. The corona attaches one copy of the second factor at each vertex of the first factor, joining that copy to the corresponding closed neighborhood.
