---
bibkey: albright2023kemenyedgederivative
authors: C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix
year: 2023
title: On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant
doi: 10.48550/arXiv.2211.01495
url: https://arxiv.org/abs/2211.01495v2
claim: "Conjecture 3.5 asserts that the path-ends non-edge minimizes the edge derivative of Kemeny's constant among simple graphs of a fixed order."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2211.01495

Source: https://arxiv.org/abs/2211.01495v2

The version is v2, 13 July 2023. Page numbers refer to its printed pages.

## Definitions

Section 1, page 3, states:

> Kemeny’s constant can be computed as

$$
K(G)=\sum_{\lambda_T\ne1}\frac1{1-\lambda_T}
=\sum_{\lambda_L\ne0}\frac1{\lambda_L},
$$

> where each λL is an eigenvalue of L.

Section 1, page 3, states:

> The normalized Laplacian matrix of a graph is given by L = I − D^{−1/2} A D^{−1/2} where A is the adjacency matrix and D is the degree diagonal matrix.

The degree diagonal $D$ contains the row sums of $A$.
The Lean expression retains the nonzero characteristic roots with multiplicity.

Section 2, page 3, states:

> Aksoy et al. in [2] represented M(t) = A + tB where A is the adjacency matrix of a graph G and B is a symmetric matrix representing a collection of edges.

> We will not restrict B and instead have B be a symmetric matrix representing any collection of edges denoted EC.

Section 1, page 3, also states:

> Here, we assume all unweighted edges have weight 1 and all non-edges have weight 0.

For one unordered pair of distinct vertices $a,b$, the perturbation is
$B=E_{ab}+E_{ba}$. Degrees change with the perturbation, as in Figure 2.

## Conjecture 3.5

Page 19 states verbatim:

> For a given n, the derivative of Kemeny’s constant on simple graphs of order n is smallest on the path on n vertices with respect to the non-edge connecting the ends of the path. The value of this derivative is O(n³).

The Lean `claim` expresses the first sentence on connected simple graphs on
`Fin n`, with $n\ge2$ and distinct endpoints. Each compared derivative is
specified by `HasDerivAt` at zero. The path endpoints are $0$ and $n-1$.
The second sentence about the path derivative's growth is not the proposition
refuted by this module.

## Refutation and scope

The counterexample has 23 vertices. Its two cliques have vertex sets
$\{0,\ldots,7\}$ and $\{8,\ldots,15\}$; they are joined by
$0,16,17,18,19,20,21,22,8$. Adding weight at the missing chord $\{0,8\}$
gives derivative $-7683669/4096$, whereas the path-ends derivative on
$P_{23}$ is $-77763/44$. Their difference is $-4891047/45056<0$.
Grounded inverse certificates and Hermitian spectral decomposition connect
these rational values to the source's eigenvalue definition.

No minimum counterexample order, infinite family, asymptotic global optimum,
or change to the source's independently proved bounds is asserted here.

## Literature boundary

The literature screen recorded in issue #19527 is partial. It distinguishes
the degree-preserving perturbations in Bini–Meini–Poloni,
arXiv:2508.21506, and the questions about Kemeny's constant itself in
Abiad et al., arXiv:2609.17481. Completeness and priority remain
ASSUMED-UNVERIFIED.
