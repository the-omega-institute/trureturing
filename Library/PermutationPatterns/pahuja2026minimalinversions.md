---
bibkey: pahuja2026minimalinversions
authors: Nimisha Pahuja
year: 2026
title: "Minimal Inversions in Integer Matrices of Fixed RSK Shape"
doi: null
url: https://arxiv.org/abs/2602.14931v1
claim: "Conjecture 1.1: every minimal nonnegative integer matrix of a partition shape with n positive parts is symmetric and Hankel."
strata_touched:
  - D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null
Source: https://arxiv.org/abs/2602.14931v1

Section 1, Conjecture 1.1, page 2; Section 3, pages 5–6, the generalised
permutation and Definition 3.1 of inversions; Section 3.1, page 6, insertion;
Section 4, Theorem 4.1, page 8, the two-row proof, and pages 8–9, the restated
conjecture. Crossref's title query returned no matching publication DOI.

# Minimal inversions at fixed RSK shape

Conjecture 1.1, page 2, reads verbatim:

> Let $\lambda$ be a partition with $n$ parts, and let
> $M=(m_{i,j})_{1\le i,j \le n} \in \mathcal{M}_\lambda$
> be a minimal matrix of shape $\lambda$. Then $M$ is symmetric, that is,
> \[
> m_{i,j} = m_{j,i} \quad \text{for all } 1 \le i,j \le n.
> \]
> Moreover, every minimal matrix of shape $\lambda$ is Hankel: there exists a sequence of integers
> \[
> s_2, s_3, \dots, s_{2n}
> \]
> such that
> \[
> m_{i,j} = s_{i+j}
> \quad \text{for all } 1 \le i,j \le n.
> \]

Section 1, page 1: “In this setting, the shape of a matrix is defined to be the common shape of the resulting pair of semistandard Young tableaux.”

Section 1, page 2: “A matrix $M \in \mathcal{M}_\lambda$ that attains this minimum will be called a *minimal matrix of shape* $\lambda$. This matrix need not be unique.” The preceding sentence fixes the minimum over matrices of size $n\times n$ and shape $\lambda$.

Section 3, page 6: “A matrix $M=(m_{i,j})$ of size $n \times n$ can be written in a two-line notation as a generalised permutation by listing each pair $(i,j)$ exactly $m_{i,j}$ times. That is, we expand each entry of the matrix into repeated pairs.” The top row is weakly increasing; for equal top entries the bottom row is weakly increasing. The matrix word used here is the bottom row of this array, rather than the tableau row-word of Definition 3.5.

Definition 3.1, page 6: “An *inversion* of a matrix $M \in \mathcal{M}_\lambda$ is a pair of positions $(i,j)$ and $(k,l)\}$ such that $m_{ij},m_{kl}>0$, and $i<k$ and $j>l$.” The following display defines the total as $\sum_{i<k,\;j>l}m_{i,j}m_{k,l}$.

Section 3.1, page 6: “If $x_1$ is greater than or equal to all entries in $R_1$, append $x_1$ at the end of $R_1$. Otherwise, let $x_2$ be the smaller entry in $R_1$ that is strictly greater than $x_1$. Replace $x_2$ by $x_1$, and the bumped entry $x_2$ is then inserted into the second row $R_2$. This bumping process continues row by row until an entry is added at the end of some row $R_s$.” Weakly increasing rows make the first strictly larger entry the specified entry.

The encoding uses nonnegative natural entries, zero-based `Fin n` indices and letters, and exactly $n$ positive nonincreasing parts. The integer sequence in the Hankel clause is extended to $\mathbb N\to\mathbb Z$; its index shifts by two relative to the printed $s_2,\ldots,s_{2n}$. Values outside the used indices impose no restriction.

A matrix of shape $(8,8,1,1)$ has inversion count $43$, whereas every Hankel matrix of that shape has at least $45$. A minimum exists because inversion counts are natural numbers, so every minimizer of this shape is non-Hankel. The source's two-row Theorem 4.1 is outside this four-row counterexample. Theorem 1.2 and the subsequent formula for all minima retain their explicit conjectural assumption; that assumption fails in general.
