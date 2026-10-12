---
bibkey: fiolmartinezmontoyariosfukelman2020quiver
authors: B. Fiol; J. Martínez-Montoya; A. Rios Fukelman
year: 2020
title: "The planar limit of N=2 superconformal quiver theories"
doi: 10.1007/JHEP08(2020)161
url: https://arxiv.org/abs/2006.06379v2
claim: "Section 2.2, Conjecture 1 asserts that tree Ising polynomials with arbitrary positive configuration weights have all their x roots on the unit circle."
strata_touched:
  - D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1007/JHEP08(2020)161

Source: https://arxiv.org/abs/2006.06379v2

## Tree construction

Section 2.2, printed page 13 (PDF page 14), states:

> Take the graph G to be a tree T,
>
> 1. Assign a positive integer $n_i$ to each of the $e$ edges of the tree graph.
> 2. For every edge, split $n_i$ into two positive integers, $n_i=k_i+(n_i-k_i)$ and assign each of these two integers to one of the vertices at the ends of that edge.
> 3. Then, if a vertex has degree $d_j$ this procedure assigns to that vertex $d_j$ integers. Let $m_j$ be the sum of these integers at a given vertex; the magnetic field at that vertex is then $m_j H$.

Equation (2.30) is

$$
P(\tau,x,n_1,\dots,n_e)=
\sum_{k_1=1}^{n_1-1}\cdots\sum_{k_e=1}^{n_e-1}
\rho(k_i,n_i)\sum_{\text{all states}}
\tau^{e_\pm}\prod_{\text{vertices with spin up}}x^{m_j}.
$$

The accompanying sentence is:

> where $\rho(k_i,n_i)$ is a distribution that weights different configurations.

Here $e_\pm$ counts edges joining opposite spins. Equation (2.31) specifies
physical weights through binomial factors and the vertex factors $\mathcal V_i$.

## Conjecture 1

Section 2.2, printed page 14 (PDF page 15), states:

> Conjecture 1: For any tree with $e$ edges, any fixed positive integers $n_1,\dots,n_e$ and arbitrary $\rho(k_i,n_i)>0$ the polynomials $P(\tau,x,n_1,\dots,n_e)$ have all their $x$ roots on the unit circle.

The one-edge case, equations (2.32)–(2.33), is proved for $|\tau|\le1$
and arbitrary positive $\rho(n,k)$ through the palindromic-polynomial theorem
of Lakatos and Losonczi cited as reference [30].

## Formal scope

Issue [#15357](https://github.com/the-omega-institute/trureturing/issues/15357)
fixes the encoding: finite vertex and edge types, an injective list of undirected
edges whose graph is a tree, and an orientation recording which endpoint receives
$k_i$. The split sum uses $1\le k_i\le n_i-1$ with $n_i\ge2$, excluding
the empty-sum case $n_i=1$. Spins are Boolean, spin up is `true`, the coefficients
are real, and $\tau\in[-1,1]$. The weight is an arbitrary positive joint
function of the entire split configuration.

The repository refutation uses the three-vertex path oriented $0\to1\leftarrow2$,
$n=(4,4)$, $\tau=-1$, and the positive joint weight matrix
$W_{31}=\begin{pmatrix}1&1&1\\1&10&1\\1&1&31\end{pmatrix}$.
The vertex masses are $(k_1,8-k_1-k_2,k_2)$ on the allowed splits.
The same polynomial arises from $0\to1\to2$ with the second weight index reversed.
The kernel-checked settling result concerns this arbitrary-joint-weight scope.
The product-weight and physical-weight versions remain open.
