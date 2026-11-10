---
bibkey: barrettevansfrancis2017resistance
authors: Wayne Barrett; Emily J. Evans; Amanda E. Francis
year: 2017
title: Resistance distance in straight linear 2-trees
doi: 10.1016/j.dam.2018.10.043
url: https://arxiv.org/abs/1712.05883v1
claim: "Definition 43 specifies straight linear k-trees by 0 < |i-j| ≤ k; Conjecture 44 asserts the all-k endpoint resistance increment limit 6/(k(k+1)(2k+1))."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/LinearKTreeBoundary
  - D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance
license: citation-only
triage: anchor
---

# Resistance distance in straight linear 2-trees

## Verified locator

DOI: 10.1016/j.dam.2018.10.043

Source: https://arxiv.org/abs/1712.05883v1

## Source statements

Definition 43, arXiv v1 PDF p. 20:

> A straight linear $k$-tree is a graph $G_n$ with $n$ vertices with adjacency matrix that is symmetric, banded, with the first through $k$th subdiagonals equal to one and first through $k$th superdiagonals equal to one, and all other entries equal to zero. In other words $G_n$ is the graph whose (0,1)-adjacency matrix is defined by
>
> $a_{ij}=\begin{cases}1 &\text{if $0 < |i-j| \leq k$}\\0 & \text{otherwise.}\end{cases}$

Conjecture 44, arXiv v1 PDF p. 20:

> Let $G$ be the straight linear k-tree, $k \geq 1$, with $n$ vertices and $H$ be the straight linear k-tree with $n+1$ vertices. Then
>
> $\lim_{n\rightarrow \infty} r_{H} (1, n+1) - r_G(1,n) = \frac{6}{k(k+1)(2k+1)}.$

The paper defines resistance through a unit current and its Kirchhoff equation (Section 2, PDF p. 3):

> The potential difference $v_i - v_j$ between nodes $i$ and $j$ needed to maintain this current is the *effective resistance* or *resistance distance* between $i$ and $j$ since by Ohm's law, the resistance, $r_G(i,j)$ is
>
> $r_G(i,j) = \frac{v_i-v_j}{1}=v_i-v_j.$
>
> The source vector of currents is $\mathbf{s} = \mathbf{e}_i -\mathbf{e}_j$. Then by Kirchoff's law and Ohm's law,
>
> $L(G)\mathbf{v} = \mathbf{s}.$

Evans and Francis restate the same limit as Conjecture 4.5 in *Algorithmic techniques for finding resistance distances on structured graphs*, https://arxiv.org/abs/2108.07942v2 (DOI: 10.1016/j.dam.2022.04.012).

## Encoding and scope

A vertex `i : Fin n` represents vertex `i+1` of the source. `SimpleGraph.fromRel` excludes loops and symmetrizes `Nat.dist i.val j.val ≤ k`. The sequence parameter `t` represents `n=t+2`; deleting finitely many initial sizes does not change the limit. The assertion includes existence of a unit-current voltage sequence and quantifies over every such sequence. Each positive `k` is fixed as the size tends to infinity.

The proof uses finite propagation of powers of banded matrices, stabilization of endpoint moments and a uniform geometric approximation to the inverse. Literature completeness remains ASSUMED-UNVERIFIED; this note makes no exhaustive novelty claim. The scope excludes growing `k`, uniform convergence rates, increment monotonicity and bent k-trees.
