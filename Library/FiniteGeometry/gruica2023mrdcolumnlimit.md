---
bibkey: gruica2023mrdcolumnlimit
authors: Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo
year: 2023
title: "Rank-Metric Codes, Semifields, and the Average Critical Problem"
doi: 10.1137/22M1486893
url: https://arxiv.org/abs/2201.07193v1
claim: "Problem A, published Problem 2.6, asks for the fixed-field column-growth asymptotic density of maximum rank distance codes."
strata_touched:
  - D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling
  - D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor
  - D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction
  - D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1137/22M1486893

Source: https://arxiv.org/abs/2201.07193v1

Published version: SIAM Journal on Discrete Mathematics 37(2), 1079–1117.
Problem 2.6 and Notation 2.5 occur on page 1082.

## Source question

“Problem 2.6. Compute or estimate $\delta_q^{\mathrm{rk}}(n \times m, k, d)$. In particular, compute its asymptotic behavior as $q \rightarrow +\infty$. Compute or estimate the asymptotic density of MRD codes, i.e., $\delta_q^{\mathrm{rk}}(n \times m, m(n-d+1),d)$, as $q \rightarrow +\infty$ and as $m \rightarrow +\infty$.”

The fixed-field column limit is one part of this question. The large-field
limit and arbitrary choices of the dimension are separate questions.

## Definitions

The following arXiv v1 passages fix the objects (published pp. 1081–1082):

```tex
\begin{definition}
A (\textbf{rank-metric}) \textbf{code} is a non-zero $\F_q$-subspace $\mC \le \mat$. Its \textbf{minimum distance}
is $$\drk(\mC)=\min\{\rk(M) \mid M \in \mC, \; M \neq 0\}.$$
\end{definition}
```

```tex
Throughout the paper we will extensively use the $q$-binomial coefficient of non-negative integers
i \ge j, defined as
\begin{equation}\label{def:qbin}
    \qbin{i}{j}{q}= \prod_{\ell=0}^{j-1}\frac{(q^i-q^\ell)}{\left(q^j-q^{\ell}\right)}.
\end{equation}
It is well known that $\qbin{i}{j}{q}$ counts the number of $j$-dimensional subspaces of an $i$-dimensional space over $\F_q$.
```

```tex
\begin{notation} \label{not:density}
We let
$$\delta^\rk_q(n \times m, k, d):=\frac{|\{\mC \le \mat \mid \dim(\mC)=k, \, \drk(\mC) \ge d\}|}{\qbin{mn}{k}{q}}$$ denote the \textbf{density} (\textbf{function}) of rank-metric codes having dimension $k$ and minimum distance at least $d$.
This number measures the proportion of rank-metric codes with minimum distance at least $d$ within the $k$-dimensional ones. Note that, by definition, the density function of MRD codes is given by
$$\delta^\rk_q(n \times m, m(n-d+1),d).$$
\end{notation}
```

The source's infinite-product notation on published page 1083 includes:

```tex
Notice that $\pi$ is closely related to the Euler function $\phi$, which is defined by $\phi(x)=\prod_{i=1}^\infty (1-x^i)$ for $x \in (-1,1)$. Indeed, we have $\pi(q)=1/\phi(1/q)$.
```

Here $P(q)=\phi(1/q)=1/\pi(q)$.

The Gaussian denominator counts all subspaces of dimension $k$.
The candidate column-limit value is
$$
\left(\prod_{j=1}^{\infty}(1-q^{-j})\right)^{{n\brack d-1}_q}
$$
for fixed $q,n,d$ with $2\le d\le n$. The case $d=1$ has density one.
Finite field carriers encode $q$ by their cardinality. Matrix rank, subspace
dimension, and the two finite cardinalities encode the density directly.

## Scope and evidence boundary

The tensor dimension equality criterion, mixed Gaussian kernel moments and
finite multivariate Möbius truncation provide the proposed proof mechanism.
The limit keeps the field, row count and distance fixed. It does not assert
joint distributional convergence at arbitrary nonzero nullities, or a limit
in which these parameters grow with the column count.

The literature screen in issue #26598 is bounded. Its citation completeness
is ASSUMED-UNVERIFIED. The source already attributes the case $n=d=2$ to
prior work; no originality is claimed for that special case.

The supporting finite experiment is in
`the-omega-institute/trureturing-experiments`, commit
`87c2172ec43c2a70ceaf9d0ddc77363694a4b20a`, path
`docs/reports/grss-mrd-density-fixed-field-column-limit/check.py`, SHA-256
`1ff617c874dfe76ce3ffec33c4a6afe7971bcfe0e0fa098ea211d748e1e94967`.
Issue #26598 records exit code 0 and the terminal reading `ALL_CHECKS_OK`.
This finite evidence does not prove the asymptotic claim.
