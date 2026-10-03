---
bibkey: aceska2022crossframe
authors: R. Aceska and M. Kaczanowski
year: 2022
title: "Cross-Frame Potential"
doi: 10.1080/01630563.2022.2128818
url: https://arxiv.org/abs/2205.05613v3
claim: "Conjecture 41: Let F be a frame for Fⁿ, and let G be one of its dual frames. Then µ(Gr(F, G)) ≥ √((nk − n²)/(k²(k − 1))). (21)"
strata_touched:
  - D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation
license: citation-only
triage: anchor
---

# Cross-Frame Potential

R. Aceska and M. Kaczanowski, Numerical Functional Analysis and Optimization
43 (2022), 1707–1731. Quotations and page numbers refer to arXiv:2205.05613v3.
The source's field is either the real or the complex numbers.

Definition 1, page 3, defines a frame by constants $0 < A \le B < +\infty$
such that $A\|f\|^2 \le \sum_{i=1}^k |\langle f,f_i\rangle|^2 \le B\|f\|^2$
for every $f \in H$. Its following sentence is:

> In a finite-dimensional space H, frames are simply spanning sets of H.

Definition 3, page 3:

> Let $\{f_i\}_{i=1}^k$ be a frame for $H$. A dual frame for $\{f_i\}_{i=1}^k$ is a frame $\{g_i\}_{i=1}^k$ such that for every $f \in H$,
> $f = \sum_{i=1}^k \langle f,g_i\rangle f_i = \sum_{i=1}^k \langle f,f_i\rangle g_i$.

Section 4, page 12:

> Let F = {f₁, …, fₖ} be a frame for Fⁿ, and let H = {h₁, …, hₖ} be a dual frame for F. We denote the cross-Gramian of F and H by Gr(F, H) and we denote the maximal off-diagonal magnitude of Gr(F, H) as
> $\mu(\mathrm{Gr}(F,H)) := \max_{i\ne j}|\langle f_i,h_j\rangle|$.

Conjecture 41, Section 4.2, page 17:

> Let F be a frame for Fⁿ, and let G be one of its dual frames. Then
> $\mu(\mathrm{Gr}(F,G)) \ge \sqrt{\frac{nk-n^2}{k^2(k-1)}}$. (21)

The real case is encoded by `Fin k → EuclideanSpace ℝ (Fin n)`, with `n ≤ k`
and `2 ≤ k`. The frame predicate is spanning, and the dual-frame predicate
includes that the second family spans and both reconstruction equations.
All arithmetic inside the square root is real arithmetic.

## Verified locator

- DOI: https://doi.org/10.1080/01630563.2022.2128818
- URL: https://arxiv.org/abs/2205.05613v3 — Definition 1 and Definition 3,
  page 3; off-diagonal magnitude, page 12; Lemma 33, page 13;
  Conjecture 41 and Eq. (21), page 17.
- The journal text has not been read; the source quotations are from arXiv v3.
