---
bibkey: cooperdu2025steinerdistancehypermatrices
authors: Joshua Cooper; Zhibin Du
year: 2025
title: Determinants of Steiner Distance Hypermatrices
doi: 10.48550/arXiv.2505.10501
url: https://arxiv.org/abs/2505.10501v1
claim: "is it true that the H-eigenvalues of C₁ are all positive? Does this generalize to all even k?"
strata_touched:
  - D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner
license: citation-only
triage: anchor
---

# Cooper–Du’s reflected Steiner H-eigenvalue questions

## Verified locator

Joshua Cooper and Zhibin Du, *Determinants of Steiner Distance
Hypermatrices*, arXiv:2505.10501v1 (2025). Printed page 1 defines Steiner
distance and its multilinear form. Lemma 4.2 on printed page 8 gives the
reflection. Section 4, printed pages 9–10, defines the reflected quartic
forms, states Proposition 4.5 and poses the positivity questions.
[Versioned arXiv record](https://arxiv.org/abs/2505.10501v1) ·
[DOI](https://doi.org/10.48550/arXiv.2505.10501)

## Steiner and reflected forms

The order-$k$ Steiner entry for an ordered tuple $(i_1,\ldots,i_k)$ of
vertices of a tree $T$ is the minimum number of edges in a connected
subgraph containing $\{i_1,\ldots,i_k\}$. This minimum is attained by the
unique minimal subtree spanning that vertex set. Repeated indices are
allowed. They give repeated factors in the multilinear form, while the
terminal set for the minimum includes each distinct vertex once.

For $n=|V(T)|$, the reflection $A$ through the all-ones line acts by
$(Ax)_i=2\sum_j x_j/n-x_i$. Printed page 9 defines
$C_1=M(\cdot,\cdot,\cdot,A\cdot)$ at order four. At order $k$, the same
placement is $C_1(z_1,\ldots,z_k)=M(z_1,\ldots,z_{k-1},Az_k)$.

## Questions following Proposition 4.5

Printed page 10 poses the questions in the paragraph following the
proof of Proposition 4.5. [Author PDF](https://arxiv.org/pdf/2505.10501v1#page=10)

> Thus, we ask: is it true that the H-eigenvalues of C₁ are all positive? Does this generalize to all even k?

For the last-reflected tensor, the first-slot convention uses a nonzero
real vector $x$ and a real $\lambda$ satisfying
$M(e_i,x,\ldots,x,Ax)=\lambda x_i^{k-1}$ at every vertex $i$.
The formal claim asks for strict positivity over trees on at least three
vertices and every even $k\ge 4$, including the quartic question. The
authors report computational evidence for quartic positivity. Their
Proposition 4.5 states diagonal positivity of the sum $C_1+C_3$,
where $C_3=M(\cdot,A\cdot,A\cdot,A\cdot)$. Conjecture 1 on printed
page 8 concerns the sign of the unreflected Steiner hyperdeterminant.
