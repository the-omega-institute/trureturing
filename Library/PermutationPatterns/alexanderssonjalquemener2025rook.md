---
bibkey: alexanderssonjalquemener2025rook
authors: Per Alexandersson, Aryaman Jal, and Maena Quemener
year: 2025
title: "Real-rootedness of rook-Eulerian polynomials"
doi: 10.48550/arXiv.2502.05939
url: https://arxiv.org/abs/2502.05939v1
claim: "Conjecture 28: Ferrers-board multiset rook-Eulerian real-rootedness and pairwise interlacing of the decreasing first-letter refinements."
strata_touched:
  - D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation
license: citation-only
triage: anchor
---

# Multiset rook-Eulerian polynomials

The primary source is arXiv:2502.05939v1, Section 3.3, pages 11–12.
Conjecture 28, page 12, reads:

> For Ferrers boards, the polynomial $R(\lambda,\alpha;t)$ is real-rooted. Moreover,
> $R_{\lambda_1}(\lambda,\alpha;t), R_{\lambda_1-1}(\lambda,\alpha;t), \ldots, R_2(\lambda,\alpha;t), R_1(\lambda,\alpha;t)$
> forms an interlacing sequence.

Definition 8, page 6, reads:

> Let $f$ and $g$ be polynomials with positive leading coefficients and real, non-positive zeros, $a_i$ and $b_i$, respectively. We say that $f$ interlaces $g$, and we write $f \preceq g$ if
> $\dotsm \leq a_3 \leq b_3 \leq a_2 \leq b_2 \leq a_1 \leq b_1 \leq 0$.
> Note that $\deg(f)=\deg(g)$ or $\deg(f)+1=\deg(g)$.

Definition 9, page 6, reads:

> A sequence $F=(f_1,\ldots,f_n)$ of real-rooted polynomials is interlacing if $f_i \preceq f_j$ for $1\leq i<j\leq n$.

Section 3.3, page 11, defines the words:

> Let $\alpha=(\alpha_1,\ldots,\alpha_k)$ be non-negative integers with total sum $n$, and let $\lambda$ and $\mu$ be integer partitions such that $\lambda_i>\mu_i$ for all $i$. We let $\mathcal W(\lambda/\mu,\alpha)$ be all words with $\alpha_i$ entries equal to $i$, such that $\mu_i<w_i\leq\lambda_i$ for all $i=1,2,\ldots,n$.

For Ferrers boards, $\mu=0$. Equations (10) and (11) define
$R=\sum_{w\in\mathcal W}t^{\operatorname{asc}(w)}$ and
$R_j=\sum_{w\in\mathcal W,\,w_1=j}t^{\operatorname{asc}(w)}$.
Section 2, page 4, specifies:

> if $w_1w_2\dotsc w_\ell$ is a word, then $i$ is an ascent of the word if $w_i<w_{i+1}$.

Examples 25–26 give twelve fitting rearrangements of $11223$ on board $22233$,
with polynomial $t^3+8t^2+3t$.
The source cites Simion for rectangular-board real-rootedness and Ma–Pan,
Theorem 1.11, for interlacing in the rectangular case. Conjecture 28 concerns
arbitrary Ferrers boards.

The six-row board $(3,3,3,3,4,4)$ with content $(2,2,1,1)$ refutes the
interlacing conjunct: the required bottom comparison is
$-7\leq-4-\sqrt{13}$. The universal real-rootedness conjunct remains open.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2502.05939
- URL: https://arxiv.org/abs/2502.05939v1
- Version and location: arXiv:2502.05939v1; Section 2, page 4 for ascents;
  Definitions 8–9, page 6 for interlacing; Section 3.3, page 11 for words,
  equations (10)–(11) and Examples 25–26; Conjecture 28, page 12.
