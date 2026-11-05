---
bibkey: monterde2022strongcospectralitytwins
authors: Hermie Monterde
year: 2022
title: "Strong cospectrality and twin vertices in weighted graphs"
doi: 10.13001/ela.2022.6721
url: https://arxiv.org/abs/2111.01265v2
claim: "The paper studies strong cospectrality of vertices with respect to generalized adjacency and normalized adjacency matrices of weighted graphs, relates it to twin vertices, recalls the Arnadottir-Godsil bound |V(X)|/n on pairwise adjacency strongly cospectral vertices of normal Cayley graphs, where n is the largest eigenvalue multiplicity of A, and asks whether this bound holds for other classes of graphs and in general for generalized adjacency matrices."
strata_touched:
  - D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation
license: citation-only
triage: anchor
---

# Strong cospectrality and twin vertices in weighted graphs

H. Monterde, arXiv:2111.01265v2; The Electronic Journal of Linear Algebra 38 (2022), 494–518. Quotations are from the v2 TeX source.

Generalized adjacency matrices:

> Let $\alpha,\beta,\gamma\in\mathbb R$ with $\gamma\neq 0$. A *generalized adjacency matrix* $\textbf{A}(X)$ of $X$ is a matrix of the form $\textbf{A}(X)=\alpha I+\beta D(X)+\gamma A(X).$

> Note that if $\alpha=\beta=0$ and $\gamma=1$, then $\textbf{A}=A$

Spectral decomposition and strong cospectrality:

> Let $H$ be an $m\times m$ Hermitian matrix. Then $\sigma(H)\subseteq \mathbb R$ and $H$ admits a spectral decomposition $H=\sum_{j}\lambda_jE_j$ where the $\lambda_j$'s are the distinct eigenvalues of $H$ and each $E_j$ is the orthogonal projection matrix onto the eigenspace associated with $\lambda_j$.

> *parallel* if $E_j\textbf{e}_u$ and $E_j\textbf{e}_v$ are parallel vectors for each $j$, i.e., for each $j$, there exists $c\in\mathbb C$ such that $E_j\textbf{e}_u=cE_j\textbf{e}_v$,

> *strongly cospectral* if for each $j$, (\ref{parallel}) holds for some $c\in\mathbb C$ with $|c|=1$.

> If $H$ is real symmetric, then $u$ and $v$ are parallel with respect to $H$ if the constant $c$ in (\ref{parallel}) is real, and strongly cospectral with respect to $H$ if $E_j\textbf{e}_u=\pm E_j\textbf{e}_v$ for each $j$

The question (Section 3, PDF p. 15 of v2):

> We mention an interesting result of Árnadóttir and Godsil which states that if $X$ is a normal Cayley graph and $n$ is the largest multiplicity of an eigenvalue of $A$, then the number of pairwise adjacency strongly cospectral vertices is bounded above by $|V (X)|/n$ [4, Theorem 6.1]. It would be interesting to check whether this bound holds for other classes of graphs, and in general whenever $M=\textbf{A}$.

## Verified locator

Source: https://arxiv.org/abs/2111.01265v2
- URL: https://arxiv.org/abs/2111.01265v2 (the e-print is a tar archive; member `ELA-sample1_copy.tex`, md5 `21a1ee53b9e64ae0b3a6773aa4fdbb45`, 1444 lines):
  - generalized adjacency matrices, l. 143–150, and the adjacency special case, l. 161;
  - spectral decomposition, parallelism and strong cospectrality, l. 170–192;
  - the question after Theorem 3.11, l. 727.
- DOI: 10.13001/ela.2022.6721 (https://doi.org/10.13001/ela.2022.6721; Crossref lists The Electronic Journal of Linear Algebra, pages 494–518, published 10 September 2022, without a volume field; the arXiv journal reference gives volume 38).
