---
bibkey: chafaidadounyoussef2024logenergy
authors: Djalil Chafaï; Benjamin Dadoun; Pierre Youssef
year: 2024
title: Monotonicity of the logarithmic energy for random matrices
doi: 10.1142/S2010326324500084
url: https://arxiv.org/abs/2212.06090v2
claim: Question 1.3 asks for decreasing penalized logarithmic energy of mean sample-covariance spectral measures and convergence to the square Marchenko–Pastur energy.
strata_touched:
  - D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Asymptotics/chafaidadounyoussef2024logenergy -->
# Logarithmic energy of sample covariance matrices

## Verified locator

DOI: 10.1142/S2010326324500084

Source: https://arxiv.org/abs/2212.06090v2

The statement below is Question 1.3, PDF p. 4, in arXiv v2.
The journal article appears in *Random Matrices: Theory and Applications*
13(2), article 2450008. Agreement of the journal text with arXiv v2 is
ASSUMED-UNVERIFIED.

## Source definitions and question

> For an $n\times n$ matrix~$A$ with entries in~$\mathbb{C}$, we denote by $\lambda_1(A),\ldots,\lambda_n(A)$ its eigenvalues, which are the roots in~$\mathbb{C}$ of its characteristic polynomial $z\mapsto\det(A-z\mathrm{Id}_n)$, viewed as a multiset of~$n$ elements. We denote the empirical spectral distribution by
>
> \[
> \mu_A\coloneqq\frac{1}{n}\sum_{k=1}^n\delta_{\lambda_k(A)}.
> \]
> Let $\mathcal{P}_2(K)$ be the set of probability measures on~$K$ where~$K=\mathbb{R}$ or~$K=\mathbb{C}$, with finite second moment
> $m_2\coloneqq\int|x|^2\mathrm{d}\mu(x)<\infty$. The logarithmic energy
> $\mathcal{E}\colon\mathcal{P}_2(K)\to(-\infty,\infty]$ is defined by
> \begin{equation*}
>   \mathcal{E}(\mu)
>   \coloneqq\iint\log\frac{1}{|x-y|}\,\mu(\mathrm{d} x)\mu(\mathrm{d} y),
> \end{equation*}
> which makes sense since
> $(x,y)\in\mathbb{C}^2\mapsto\frac{|x|^2+|y|^2}{2}-\log|x-y|$ is bounded below
> by a finite constant.
> Finally, we consider the square Marchenko--Pastur law given by $\mu_{\mathrm{MP}}\coloneqq \frac{{\sqrt{(4-x)}_+}}{2\pi \sqrt{x}}\,\mathrm{d} x$. This law appears in particular as the limiting spectral distribution of $\frac{1}{n}X_nX_n^*$ where $X_n=(\xi_{ij})_{1\leq i,j\leq n}$ is an~$n\times n$ random matrix whose entries are i.i.d.\ centered complex random variables of unit variance. The starting point is again a variational characterization for $\mu_{\mathrm{MP}}$ (see~\cite[Proposition~5.5.13]{Hiai00}):
> \[
> \mu_{\mathrm{MP}}= \operatorname{argmin}_{\substack{\mu\in\mathcal{P}_2(\mathbb{R}_+)\\m_1(\mu)=1}}\mathcal{E}
>   =\operatorname{argmin}_{\mu\in\mathcal{P}_2(\mathbb{R}_+)}\mathcal{E}^{(1)},
> \]
> where
> \[
> \mathcal{E}^{(1)}(\mu) \coloneqq \mathcal{E}(\mu)+m_1(\mu).
> \]
> Let~$X_n\coloneqq(\xi_{ij})_{1\leq i,j\leq n}$ be an~$n\times n$ random matrix whose entries are i.i.d.\ centered complex random variables of unit variance, and let $\mu_n\coloneqq\mu_{\frac{1}{n}X_nX_n^*}$ be the corresponding spectral distribution. Is it true that $\mathcal{E}^{(1)}(\mathbb{E}\mu_n)\searrow \mathcal{E}^{(1)}(\mu_{\mathrm{MP}})$?

The square Gram matrix is normalized by its dimension. Eigenvalues are
counted with algebraic multiplicity, and the expectation is taken before
computing the logarithmic energy. The monotone arrow means consecutive
nonincrease together with convergence. The energy uses extended real
values and retains the diagonal singularity.

## Scope

The covariance refutation concerns a fixed centered entry law of unit
second moment, obtained by adding circular complex Gaussian noise to a
Bernoulli law with rare probability 1/256. It compares dimensions two and
three. The Gaussian and Laguerre results in the source remain intact.

The literature screen recorded in issue #27294 found no settlement of the
covariance question in its searched scope. Completeness of that screen is
ASSUMED-UNVERIFIED.
