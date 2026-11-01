---
bibkey: barrett2022laplacianspread
authors: Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton
year: 2022
title: "On the Laplacian spread of digraphs"
doi: 10.48550/arXiv.2206.15410
url: https://arxiv.org/abs/2206.15410v1
claim: "Conjecture 14 excludes balanced digraphs of spread strictly between zero and one; Conjecture 20 proposes a universal slope-one bound."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation
  - D5/S3/Combinatorics/SpectralGraph/BarrettBalancedLaplacianSpreadGap
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2206.15410

Source: https://arxiv.org/abs/2206.15410v1

Conjecture 14, page 15: “There is no balanced digraph that satisfies $0<\operatorname{sp}(\Gamma)<1$.”

Conjecture 20, page 16: “The bound on the Laplacian spread of digraphs given in (5) can be reduced to a linear function in $n$ with a slope of $1$.”

Section 6: “Note that all conjectures are made for unweighted digraphs.”

Section 2, page 2: “We denote the out-degree of vertex $i\in V$ by $d^{+}(i)$, which is equal to the number of edges of the form $(i,j)\in E$.”
“Similarly, we denote the in-degree of vertex $i\in V$ by $d^{-}(i)$, which is equal to the number of edges of the form $(j,i)\in E$.”
“After indexing the vertex set as $V=\{1,2,\ldots,n\}$, we define the adjacency matrix of $\Gamma$ by $A=[a_{ij}]_{i,j=1}^{n}$, where $a_{ij}=1$ if $(i,j)\in E$ and $a_{ij}=0$ otherwise.”
“Moreover, we define the Laplacian matrix of $\Gamma$ by $L=D-A$, where $A$ is the adjacency matrix of $\Gamma$ and $D$ is a diagonal matrix whose $i$th diagonal entry is $d^{+}(i)$.”

Section 2, page 2: “The algebraic connectivity of $\Gamma$ is given by”

$$\alpha(\Gamma)=\min_{\substack{\mathbf{x}\perp\mathbf{e}\\\|\mathbf{x}\|=1}}\mathbf{x}^{T}L\mathbf{x}.$$

“Another related and useful quantity is”

$$\beta(\Gamma)=\max_{\substack{\mathbf{x}\perp\mathbf{e}\\\|\mathbf{x}\|=1}}\mathbf{x}^{T}L\mathbf{x}.$$

Section 3, pages 4–5: “We define the Laplacian spread of a digraph $\Gamma$ by”

$$\operatorname{sp}(\Gamma)=\beta(\Gamma)-\alpha(\Gamma),$$

“that is, $\operatorname{sp}(\Gamma)$ is equal to the length of the real part of $W_r(L)$.”

Section 4, page 9: “Now, let $\Gamma=(V,E)$ be a balanced digraph, that is, $d^{+}(i)=d^{-}(i)$ for all $i\in V$.”

The encodings use real Euclidean vectors indexed by `Fin n`, zero coordinate sum, and unit Euclidean norm. Their literal quadratic-value set has infimum `alpha` and supremum `beta`; for every $n\ge2$ the set is nonempty and compact, so these are the stated minimum and maximum. Looplessness is explicit; symmetry is not assumed. The graph is unweighted and both opposite arcs may occur. The journal version is *Linear Algebra and its Applications* 664 (2023), 126–146, DOI 10.1016/j.laa.2023.01.016; the mathematical statements compared here are arXiv v1.

Literature completeness is ASSUMED-UNVERIFIED. The journal text, complete citing-work inventory, latest Li–Ji corrigendum, Gregory–Hershkowitz–Kirkland nonprincipal-spectrum implications, and Cameron–Graillat text remain unverified in the source screen recorded by issues #21873 and #21874.
