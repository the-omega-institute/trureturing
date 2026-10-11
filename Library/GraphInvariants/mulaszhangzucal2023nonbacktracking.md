---
bibkey: mulaszhangzucal2023nonbacktracking
authors: R. Mulas; D. Zhang; G. Zucal
year: 2024
title: "There is no going back: Properties of the non-backtracking Laplacian"
doi: 10.1016/j.laa.2023.10.014
url: https://arxiv.org/abs/2303.00373v2
claim: "Conjecture 5.3: If G is not the cycle graph, then ε ≤ 1/(δ−1)."
strata_touched:
  - D5/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing
  - D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree
license: citation-only
triage: anchor
---

# Non-backtracking Laplacian gap

Section 1 defines the non-backtracking graph on oriented edges and its random-walk Laplacian
\(\mathcal L = \mathrm{id} - \mathcal D^{-1}\mathcal A\). Section 5 defines the gap
\(\varepsilon=\min_{\lambda\in\sigma(\mathcal L)}|1-\lambda|
=\min_{\lambda\in\sigma(\mathcal D^{-1}\mathcal A)}|\lambda|\).

## Conjecture 5.3

The paper states verbatim on printed page 16: “If \(G\) is not the cycle graph, then
\(\varepsilon\leq \frac{1}{\delta-1}\).”

The settling module proves the stronger statement for every finite simple graph of minimum degree
at least two, retaining the source's cycle exclusion in `claim`. For minimum degree at least three
the proof produces a positive real eigenvalue; the minimum-degree-two case uses the all-ones
eigenvector.

## Verified locator

DOI: 10.1016/j.laa.2023.10.014

Source: https://arxiv.org/abs/2303.00373v2
