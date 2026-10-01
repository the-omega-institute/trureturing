---
bibkey: godsil2023diagonal
authors: Chris Godsil; Krystal Guo; Mariia Sobchuk
year: 2023
title: "Diagonal entries of the average mixing matrix"
doi: 10.48550/arXiv.1910.02039
url: https://arxiv.org/abs/1910.02039v1
claim: "For a graph X with adjacency matrix A = sum_r theta_r E_r (E_r the projection onto the theta_r-eigenspace), the average mixing matrix of the continuous quantum walk is the sum of the Schur squares E_r o E_r; the trace of the average mixing matrix of K_n is (n^2 - 2n + 2)/n, regular graphs have trace at most that of K_n (Corollary 6.3), and the paper conjectures (Conjecture 9.1 of the journal version) that the complete graph on n vertices attains the maximum trace with respect to the adjacency matrix for all n."
strata_touched:
  - D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum
license: citation-only
triage: anchor
---

# Diagonal entries of the average mixing matrix

Chris Godsil, Krystal Guo and Mariia Sobchuk, arXiv:1910.02039v1
[math.CO, cross-listed to quant-ph] (2019); Australasian Journal of
Combinatorics 86(3) (2023) 373–386. Quotations are from the arXiv source,
with its notation macros expanded and cross-references given by their
numbers.

The mixing matrix of the continuous quantum walk with transition matrix
$U(t)$ and its average are defined in the introduction:

> In this paper we focus on a matrix derived from $U(t)$, the \textsl{mixing matrix} of the walk, which we define by $M(t) = U(t) \circ \overline{U(t)}$. (Here $\circ$ denotes the Schur product of two matrices.) The \textsl{average mixing matrix}, denoted $\widehat{M}$, is defined as follows: $\widehat{M}(X) = \lim_{T\to\infty}\frac1T \int_0^T M(t)\,dt.$

Section 2 gives the spectral form, quoting Godsil (2013):

> Let $X$ be a graph on $n$ vertices and let $B \in \{A(X), L(X)\}$. Let $\theta_1, \ldots, \theta_d$ be the distinct eigenvalues of $B$ and, for $r=1,\ldots,d$, let $E_r$ be the idempotent projection onto the $\theta_r$ eigenspace of $B$

> Let $X$ be a graph and let $B \in \{A(X), L(X)\}$. Let $B = \sum_{r=0}^d \theta_r E_r$ be the spectral decomposition of $B$. The average mixing matrix of $X$ with respect to $B$ is $\widehat{M}(B) = \sum_{r=0}^d E_r \circ E_r.$

Section 6 evaluates the complete graph and compares regular graphs
(Corollary 6.3):

> The trace of $\widehat{M}(A(K_n))$ is $\frac{1+(n-1)^2}{n} = \frac{n^2-2n + 2}{n}.$

> If $X$ is a regular graph on $n$ vertices, then $\operatorname{tr}\widehat{M}_A(X) \leq \operatorname{tr}\widehat{M}_A(K_n)$.

Table 2 lists $K_n$ as the graph on $n$ vertices of maximum trace with
respect to the adjacency matrix for $n = 3, \ldots, 8$. Section 9, "Open
problems", closes with:

> Based on the computations summarized in Table 2 and on Corollary 6.3, we also make the following conjecture. The complete graph on $n$ vertices attains the maximum trace with respect to the $\widehat{M}_{A}$ for all $n$.

The empty graph on $n$ vertices has $\widehat{M}_A = I$ and trace $n$, so
the maximum is over connected graphs. The paper's Laplacian results on the
maximum trace are stated for connected graphs, and A. Mohan, C. Tamon,
Y. Xu and H. Zhan, *Laziness of Quantum Walks on Graphs*,
arXiv:2608.20739 (2026), restate the conjecture as: "It is conjectured in
[Godsil2023] that $K_n$ maximizes $\operatorname{tr}(X)$ relative to the
adjacency matrix over all connected graphs on $n$ vertices."

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1910.02039 (the arXiv record; the
  journal version, Australas. J. Combin. 86(3) (2023) 373–386, states the
  conjecture as Conjecture 9.1, and its text was read by a scout subagent).
- URL: https://arxiv.org/abs/1910.02039v1 (the e-print is the single
  gzipped file `avgtr-arxiv.tex`, md5 `b5102f5073d9c1687d09772dfa18dd7a`;
  the conjecture is at l. 1149–1151): the spectral form of the average
  mixing matrix (Section 2), the trace at the complete graph and
  Corollary 6.3 (Section 6), Table 2 (Section 8) and the conjecture
  (Section 9).
