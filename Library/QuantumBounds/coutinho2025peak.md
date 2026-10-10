---
bibkey: coutinho2025peak
authors: Gabriel Coutinho, Krystal Guo, Vincent Schmeits
year: 2025
title: "Peak state transfer in continuous quantum walks"
doi: 10.48550/arXiv.2505.11986
url: https://arxiv.org/abs/2505.11986v4
claim: "Section 3 defines the bounding matrix and peak state transfer; Lemma 5.2 characterizes phase alignment; Open Problem 7.1 asks for infinitely many non-star trees admitting Laplacian peak state transfer."
strata_touched:
  - D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2505.11986

Source: https://arxiv.org/abs/2505.11986v4

DOI URL: https://doi.org/10.48550/arXiv.2505.11986

## Definitions and phase alignment

Section 3, p. 5, uses the distinct-eigenvalue spectral decomposition
$M=\sum_{r=0}^d\theta_r E_r$ and states:

> $E_r$ is the idempotent projection onto the $\theta_r$-eigenspace.

> In particular, the transition matrix of the continuous-time quantum walk on $M$ can be written as the following matrix-valued function in time:
> $U(t)=e^{itM}=\sum_{r=0}^d e^{it\theta_r}E_r$.

> We will refer to $B(M):=\sum_{r=0}^d |(E_r)|$ as the bounding matrix of $M$, as the $(v,u)$-entry of $B(M)$ upper-bounds $|U(t)_{v,u}|$ for all values of $t$.

Absolute values are entrywise.

> For distinct vertices $u,v$, we say that there is peak state transfer from $u$ to $v$ with respect to $M$ if there exists a time $\tau$ such that
> $|U(\tau)_{v,u}| = B(M)_{v,u}$.

Laplacian dynamics uses $M=L(G)=D-A$. Lemma 5.2, p. 8, states that the triangle bound
is attained exactly when the phases on the positive and negative mutual spectral support
are respectively $\gamma$ and $-\gamma$ for a common complex phase.

## Open Problem 7.1

Section 7, p. 21, states:

> Determine whether infinitely many such trees, not isomorphic to the star graph, admit Laplacian peak state transfer.

Figure 10, p. 22, depicts $K_{1,3}$, $K_{1,4}$, and a 10-vertex rooted tree with
three hubs and two leaves on each hub. The source presents these as examples found by computation.

The Lean definitions use `G.lapMatrix ℝ`, the eigenbasis-filtered sum of outer products for
each spectral idempotent, a sum over the finite image of eigenvalues for `boundingEntry`,
and the complex matrix exponential for `lapPropagator`. The new result constructs
arbitrarily large non-star trees and proves peak transfer from the root to each hub at time $\pi$.
