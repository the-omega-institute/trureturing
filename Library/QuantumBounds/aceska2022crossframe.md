---
bibkey: aceska2022crossframe
authors: R. Aceska and M. Kaczanowski
year: 2022
title: "Cross-Frame Potential"
doi: 10.1080/01630563.2022.2128818
url: https://arxiv.org/abs/2205.05613v3
claim: "Conjecture 41: Let F be a frame for Fⁿ, and let G be one of its dual frames. Then µ(Gr(F, G)) ≥ √((nk − n²)/(k²(k − 1))). (21) Conjecture 42: If a frame F for F^n forms an exclusive Grassmannian pair with one of its duals, then that dual must be the canonical dual frame of F."
strata_touched:
  - D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation
  - D5/S3/QuantumBounds/Designs/CrossFrameWelchBoundRefutation
license: citation-only
triage: anchor
---

# Cross-Frame Potential

The following quotations refer to arXiv:2205.05613v3. The journal publication is
Numerical Functional Analysis and Optimization 43 (2022), 1707–1731.

Definition 1 (p. 3):

> A sequence of vectors F = {f_i}_{i=1}^k, with k ≥ n, in an n-dimensional Hilbert space H is a frame for H if there exist real constants 0 < A ≤ B < +∞ such that

$$A\|f\|^2 \le \sum_{i=1}^k |\langle f,f_i\rangle|^2 \le B\|f\|^2$$

> for every f ∈ H.

The sentence immediately following Definition 1 states:

> In a finite-dimensional space H, frames are simply spanning sets of H.

Definition 3 (p. 3):

> Let {f_i}_{i=1}^k be a frame for H. A dual frame for {f_i}_{i=1}^k is a frame {g_i}_{i=1}^k such that for every f ∈ H,

$$f=\sum_{i=1}^k\langle f,g_i\rangle f_i=\sum_{i=1}^k\langle f,f_i\rangle g_i.$$

Over the reals, the two operator identities are transposes of one another.
The canonical dual is $\{S^{-1}f_i\}$, where
$Sx=\sum_i\langle x,f_i\rangle f_i$ (p. 4).

The off-diagonal magnitude in §4 (p. 12) is
$\mu(\operatorname{Gr}(F,H)):=\max_{i\ne j}|\langle f_i,h_j\rangle|$.

Definition 34 (p. 13):

> A frame F for F^n forms a Grassmannian pair with its dual frame F̃ if µ(Gr(F, F̃)) = min{µ(Gr(F, H)) | H is a dual frame of F}. (14)

The sentence following Definition 34 (p. 14):

> Some frames form an exclusive Grassmannian pair with their canonical dual (Example 32), while other frames (Example 31) have more than one dual frame which satisfy (14).

The explanation in §4.2 (p. 17):

> Note that the frame in Example 32 forms an exclusive Grassmannian pair with its canonical dual, that is, its canonical dual is the only dual frame that satisfies (14), while the frame in Example 31 has at least two duals which satisfy (14).

Conjecture 41 (§4.2, p. 17):

> Let F be a frame for Fⁿ, and let G be one of its dual frames. Then
> $\mu(\mathrm{Gr}(F,G)) \ge \sqrt{\frac{nk-n^2}{k^2(k-1)}}$. (21)

The real case of Conjecture 41 is encoded by `Fin k → EuclideanSpace ℝ (Fin n)`,
with `n ≤ k` and `2 ≤ k`. Its frame predicate is spanning, and its dual-frame
predicate includes both frame conditions and both reconstruction equations.
All arithmetic inside the square root is real arithmetic.

Conjecture 42 (§4.2, p. 17):

> If a frame F for F^n forms an exclusive Grassmannian pair with one of its duals, then that dual must be the canonical dual frame of F.

The real one-dimensional frame $(3,2,1)$ has the unique minimizing dual
$(1/5,2/15,2/15)$, distinct from its canonical dual $(3/14,1/7,1/14)$.
This is the counterexample formalized in
`D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation`.

## Verified locator

- arXiv v3: https://arxiv.org/abs/2205.05613v3 — Definitions 1 and 3 (p. 3),
  canonical dual (p. 4), off-diagonal magnitude (p. 12), Definition 34 (p. 13),
  exclusivity sentence (p. 14), Conjectures 41, 42 and 43 (p. 17).
- Journal DOI: https://doi.org/10.1080/01630563.2022.2128818.
  The journal text has not been checked against the arXiv conjecture.
