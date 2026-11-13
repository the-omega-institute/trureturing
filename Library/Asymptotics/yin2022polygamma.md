---
bibkey: yin2022polygamma
authors: "Li Yin"
year: 2022
title: "Monotonic properties for ratio of the generalized (p,k)-polygamma functions"
doi: 10.7153/jmi-2022-16-62
url: "https://files.ele-math.com/articles/jmi-16-62.pdf"
claim: "Conjecture 4.1 asserts decreasing finite-(p,k)-polygamma product quotients under strict majorization and an exact factorial image interval."
strata_touched:
  - D5/S3/Analytic/SeriesInequalities/YinPolygammaMajorizationRefutation
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Asymptotics/yin2022polygamma -->
# Finite polygamma majorization

## Verified locator

DOI: 10.7153/jmi-2022-16-62

Source: https://files.ele-math.com/articles/jmi-16-62.pdf

Journal of Mathematical Inequalities 16(3) (2022), 915–921. The source is the
journal PDF, with no arXiv identifier in the located metadata. Equation (1.5)
and the derivative definition are on p. 916; Conjecture 4.1 is on p. 920.
The source quotations and locator are those recorded in
[issue #24132](https://github.com/the-omega-institute/trureturing/issues/24132).

## Source definitions

Equation (1.4) prints, for p,k>0,

$$\Gamma_{p,k}(x)=\frac{(p+1)!k^{p+1}(pk)^{x/k-1}}{(x)_{p,k}},\quad x>0,$$

followed by “where $(x)_{p,k}=x(x+k)(x+2k)\ldots(x+pk)$”. The next sentence defines

$$\psi_{p,k}(x)=\frac{\Gamma'_{p,k}(x)}{\Gamma_{p,k}(x)},\qquad
\psi_{p,k}^{(m)}(x)=\frac{d^m}{dx^m}\psi_{p,k}(x).$$

The source’s finite-sum definition in (1.5) is

$$\psi_{p,k}(x)=\frac1k\ln(pk)-\sum_{n=0}^{p}\frac1{nk+x}
=\frac1k\ln(pk)-\int_0^\infty\frac{1-e^{-k(p+1)t}}{1-e^{-kt}}e^{-xt}\,dt.$$

Equation (1.6) prints

$$\psi_{p,k}^{(m)}(x)=(-1)^m m!\sum_{n=0}^{p}\frac1{(nk+x)^{m+1}}
=(-1)^{m+1}\int_0^\infty\frac{1-e^{-k(p+1)t}}{1-e^{-kt}}t^m e^{-xt}\,dt.$$

## Source statement

The strict-majorization paragraph on p.916 reads:

> Let $\alpha=(\alpha_1,\alpha_2,\cdots,\alpha_n)$ and $\beta=(\beta_1,\beta_2,\cdots,\beta_n)\in\mathbb R^n$. A n-tuple $\alpha$ is said to strictly majorize $\beta$ (in symbols $\alpha\succ\beta$) if $(\alpha_{[1]},\alpha_{[2]},\cdots,\alpha_{[n]})\ne(\beta_{[1]},\beta_{[2]},\cdots,\beta_{[n]})$, $\sum_{i=1}^{k}\alpha_{[i]}\geq\sum_{i=1}^{k}\beta_{[i]}$ for $1\leq k\leq n-1$, and $\sum_{i=1}^{n}\alpha_i=\sum_{i=1}^{n}\beta_i$ where $\alpha_{[1]}\geq\alpha_{[2]}\geq\cdots\geq\alpha_{[n]}$, $\beta_{[1]}\geq\beta_{[2]}\geq\cdots\geq\beta_{[n]}$ are rearrangements of $\alpha$ and $\beta$ in a descending order.

Conjecture 4.1, p.920, reads:

> For $p,k>0$ and every $\alpha_1,\alpha_2,\cdots\alpha_n,\beta_1,\beta_2,\cdots\beta_n\in\mathbb N$ such that $(\alpha_1,\alpha_2,\cdots,\alpha_n)\prec(\beta_1,\beta_2,\cdots,\beta_n)$, the function
>
> $$Q_{\alpha_1,\alpha_2,\cdots,\alpha_n;\beta_1,\beta_2,\cdots,\beta_n,p,k}(x)=\frac{\psi_{p,k}^{(\alpha_1)}(x)\cdots\psi_{p,k}^{(\alpha_n)}(x)}{\psi_{p,k}^{(\beta_1)}(x)\cdots\psi_{p,k}^{(\beta_n)}(x)}$$
>
> is decreasing on $(0,\infty)$ onto the interval $\left(\frac{(\alpha_1-1)!\cdots(\alpha_n-1)!}{(\beta_1-1)!\cdots(\beta_n-1)!},\frac{(\alpha_1)!\cdots(\alpha_n)!}{(\beta_1)!\cdots(\beta_n)!}\right)$.

## Mathematical scope

The finite sum (1.5) and its iterated derivatives define the functions. The two
signs in printed equation (1.6) disagree; differentiation of (1.5) gives
\((-1)^{r+1}r!\sum_{j=0}^{p}(jk+x)^{-r-1}\) for positive r. The opposite
printed finite-sum sign cancels in the equal-length product quotients.
The truncation p is a positive integer, k is a positive real, and every
order is a positive integer. The finite product and factorial expressions
fix these integer carriers. Weak decrease is encoded by `AntitoneOn`, so a
failure of weak decrease also refutes strict decrease. The assertion retains
the full image equality, rather than just an inclusion. Descending sorting
and weak majorization use the existing real-tuple owners, with natural
orders cast to reals and the source's unequal-rearrangement condition added.

For every p≥1, k>0, m≥2 and length n≥2, the constant order-m tuple and the
tuple with first orders m−1,m+1 and all remaining orders m strictly satisfy
the source's majorization condition. Their quotient is positive and strictly
below m/(m+1) at every positive x and has limit m/(m+1) at both endpoints.
The strict finite-node dispersion gap therefore excludes both weak
monotonicities. This is a repository-derived refutation, not a result
asserted by the source. Ordinary untruncated polygamma, sharp minima and
critical-point classification are outside the result.

The source's finite-truncation Theorem 1.1 and the finite-function
monotonicity mechanism cited in Section 4 cannot be assumed in this argument.
No claim about ordinary-function results of Qi or Yang–Tian follows.

## Independent experiment

Repository: `the-omega-institute/trureturing-experiments`, commit
`940a20d75846863a2c001eaf34d76e26aa29d79e`,
`docs/reports/yin-polygamma-majorization/check.py`, SHA256
`44509fde783070626a9be66f9958e3cc4df4e79c45d12530c53a5c251b1e5be8`.
Command: `python3 docs/reports/yin-polygamma-majorization/check.py`.
The recorded exit is 0, with `ALL_CHECKS_OK`. The exact readings include
Q(1)=54/85, Q(2)=2450/3783 and difference 3968/321555>0, 24 derivative
checks, 1,584 moment-gap checks, 168 embeddings and nine endpoint checks.
These finite readings do not establish the arbitrary-parameter family.
No experiment program is embedded here.

## Literature boundary

The literature screen in issue #24132 did not locate a settlement of this
exact finite-truncation conjecture. Completeness is `ASSUMED-UNVERIFIED`:
OpenAlex citing-work requests were rate limited, MathDB returned HTTP 403,
and the Yang–Tian full text and several cited bodies were unread.
The inspected later ordinary-polygamma statements do not settle the finite
version. No exhaustive novelty claim is made.
