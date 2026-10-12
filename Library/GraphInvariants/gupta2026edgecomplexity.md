---
bibkey: gupta2026edgecomplexity
authors: V. Gupta, A. Iosevich, J. Iosevich, B. Song, H. Tian
year: 2026
title: Edge complexity of graphs
doi: 10.48550/arXiv.2607.15598
url: https://arxiv.org/abs/2607.15598v1
claim: "The Remark after Corollary 3.10 asks whether the energy-equality class is closed under unrestricted weak products."
strata_touched:
  - D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2607.15598

Source: https://arxiv.org/abs/2607.15598v1

## Source question

The Remark after Corollary 3.10, page 18, states:

> Remark. The coprimality hypothesis is not merely a technicality in the present argument: it is what permits the product labeling to be viewed as a cyclic labeling. Proposition 3.7 does not prove closure under arbitrary weak products. Consequently, unrestricted closure of the equality class under the weak product has not been established. Whether such closure holds is a natural open question.

Definition 3.1, page 15, states:

> Definition 3.1. Let G and H be graphs. Their weak product G × H has vertex set V(G) × V(H), and (g₁, h₁) is adjacent to (g₂, h₂) if and only if g₁ is adjacent to g₂ in G and h₁ is adjacent to h₂ in H.

## Definitions and results

Section 1, page 1, states:

> Let G = (V, E) be a simple graph with at least one edge and |V| = N. After choosing a labeling of the vertices by Z_N, identify the adjacency matrix with the edge indicator

The displayed indicator is f : Z_N × Z_N → {0, 1}. The next sentence is “Its two-dimensional discrete Fourier transform is”, followed by the first formula below. Section 1, page 2, states “The Fourier ratio of f is” and “If fσ is the adjacency matrix produced by a vertex labeling σ, the edge complexity introduced in [7] is”, followed by the second and third formulas. The source uses

$$
\widehat f(m,n)=\frac1N\sum_{x,y\in\mathbb Z_N} f(x,y)e^{-2\pi i(mx+ny)/N},\qquad
\operatorname{FR}(f)=\frac{\|\widehat f\|_1}{\|\widehat f\|_2},\qquad
\operatorname{FR}_{\min}(G)=\min_{\sigma\in S_N}\operatorname{FR}(f_\sigma).
$$

Section 1, page 2, states “The graph energy is”, followed by E(G) = ∑_{j=1}^N |λ_j(G)| = ‖A‖_{S1}, “where λ1(G), . . . , λN(G) are the adjacency eigenvalues.”

Here the norms are the entrywise ℓ¹ norm and Frobenius norm. The energy is the sum of the absolute adjacency eigenvalues; size counts unoriented edges once.

Theorem 1.1, page 2, gives FR_min(G) ≥ E(G)/√(2s), with equality for cyclic Cayley graphs. Theorem 2.1, page 4, characterizes equality by at most one nonzero Fourier entry in each row and column. Theorem 2.8, page 7, implies that the squared adjacency matrix is circulant for an equality-attaining labeling. Proposition 3.7, page 16, and Corollary 3.10, page 18, establish weak-product closure for coprime orders and pairwise coprime orders, respectively.

## Scope of the refutation

The formal refutation treats K₃ × K₃. Each K₃ attains equality, whereas the product has size 18, energy 16 and FR_min strictly greater than 8/3. This disproves unrestricted closure. The coprime-order statements retain their hypotheses and are unaffected.
