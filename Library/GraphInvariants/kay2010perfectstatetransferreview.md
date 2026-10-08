---
bibkey: kay2010perfectstatetransferreview
authors: Alastair Kay
year: 2010
title: "A Review of Perfect State Transfer and its Application as a Constructive Tool"
doi: 10.1142/S0219749910006514
url: https://arxiv.org/abs/0903.4274v3
claim: "Lemma 6 (subsection Transfer Rate): for eigenvalues fulfilling the perfect state transfer condition, the rate M/2t_0 is perfectly achieved for an integer M if and only if the sums R_k of (-1)^n/B'(lambda_n) over the residue classes of (t_0/pi)(lambda_n - lambda_1) modulo M, k = 0, ..., M - 1, are all equal. The review conjectures that this condition cannot be fulfilled for any M > 2 and proves it for M > N/2."
strata_touched:
  - D5/S3/Quantum/Dynamics/KayTransferRateRefutation
license: citation-only
triage: anchor
---

# A review of perfect state transfer and its application as a constructive tool

A. Kay, *A Review of Perfect State Transfer and its Application as a
Constructive Tool*, arXiv:0903.4274v3 (16 June 2010); Int. J. Quantum Inf. 8,
641 (2010). The quotations are taken from the arXiv v3 source `review.tex`.

## The perfect state transfer condition

The subsection "The Symmetry Matching Condition" orders the eigenvalues of a
mirror-symmetric nearest-neighbour chain and states the condition, Eqn.
`eqn:st_cond`:

> Consider $\{\lambda_n\}$ to be an ordered set of eigenvalues, $\lambda_n<\lambda_{n+1}$. The necessary and sufficient conditions for state transfer in a symmetric chain then become that
> \begin{equation}
> \lambda_n-\lambda_{n-1}=(2m_n+1)\pi/t_0, \label{eqn:st_cond}
> \end{equation}
> where $t_0$ is the state transfer time, and $m_n$ is a positive integer (which can vary with $n$).

The subsection "Inverse Eigenvalue Problems" introduces

> $$
> B'(\lambda_n)=\prod_{m=1\neq n}^N(\lambda_n-\lambda_m),
> $$
> which is the derivative of the function $B(\lambda)=\prod_{m=1}^N(\lambda-\lambda_m)$, the characteristic polynomial of the system, evaluated at $\lambda_n$.

and recalls the weights of the eigenvectors on the first site, Eqn. `eqn:hoch`:

> In \cite{hochstadt}, it is proven that for a symmetric tridiagonal matrix,
> \begin{equation}
> |\alpha_n|^2=\frac{1}{(-1)^nB'(\lambda_n)\sum_{m=1}^N\frac{1}{(-1)^nB'(\lambda_m)}}.  \label{eqn:hoch}
> \end{equation}

## The rate lemma and the conjecture

The subsection "Transfer Rate" asks at which rate $1/t_r$ single-qubit states
can be sent through the chain when a new state is placed on the first spin
after the time $t_r$, and finds that the amplitude $\gamma_1$ on the first
site must vanish at that time. It continues:

> The following lemma allows us to prove a tighter bound of $1/t_r\leq N/4t_0$, although we conjecture a stronger condition; that there are no chains with $t_r<t_0$.

The lemma (`lemma:rate`, the sixth lemma of the source) reads:

> \begin{lemma}
> If a set of eigenvalues is chosen to fulfill the perfect state transfer condition of Eqn.~(\ref{eqn:st_cond}), then a necessary and sufficient condition to perfectly achieve the rate $M/2t_0$ for integer $M$ is that all the $R_k$ for $k=0\ldots M-1$ should be equal, where
> \begin{equation}
> R_k=\sum_{n=1}^N\frac{(-1)^n}{B'(\lambda_n)},
> \label{eqn:rate_cond}
> \end{equation}
> and the sum is restricted to those terms satisfying the condition
> $$
> \frac{t_0}{\pi}(\lambda_n-\lambda_1)\mod M=k.
> $$
> \label{lemma:rate}
> \end{lemma}

Its proof writes $\gamma_1(t)$ through Eqn. `eqn:hoch` and demands
$\gamma_1(2mt_0/M)=0$ for $m=1\ldots M-1$ and $\gamma_1(2t_0)=1$. After a
remark on composite $M$ the source states the conjecture:

> We conjecture that it is impossible to fulfill the condition of Lemma \ref{lemma:rate} for any $M>2$, although we only have a proof for $M>N/2$.

The module `D5/S3/Quantum/Dynamics/KayTransferRateRefutation` refutes this
conjecture: the eight eigenvalues $0, 31, 46, 65, 88, 107, 122, 153$ with
$t_0 = \pi$ fulfil Eqn. `eqn:st_cond` with $m = 15, 7, 9, 11, 9, 7, 15$, and
for $M = 4 = N/2$ all four sums $R_k$ equal $194/38984495395755$.

## Verified locator

- DOI: https://doi.org/10.1142/S0219749910006514 (the DOI
  10.1142/S0219749910006514 and the journal reference Int. J. Quantum Inf. 8,
  641 (2010) are those listed by the arXiv API for 0903.4274, read 2026-10-08).
- arXiv: https://arxiv.org/abs/0903.4274v3 (source file `review.tex`):
  Eqn. `eqn:st_cond` in the subsection "The Symmetry Matching Condition", $B'$
  and Eqn. `eqn:hoch` in the subsection "Inverse Eigenvalue Problems", the
  lemma `lemma:rate` and the conjecture in the subsection "Transfer Rate", the
  fourth subsection of the third section, "Higher Excitation Subspaces".
