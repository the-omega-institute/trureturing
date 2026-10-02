---
bibkey: rosenzweig2026loglaplacian
authors: B. Rosenzweig; J. Stanfill
year: 2026
title: "On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians"
doi: 10.48550/arXiv.2606.04225
url: https://arxiv.org/abs/2606.04225
claim: "Open Problem 1.3: Show that p_{2m,S_1}(1/2-m) is nonzero for all positive natural m, with S_1 as in equation (1.8)."
strata_touched:
  - D5/S3/ArithSums/LogLaplacianBellNonvanishing
license: citation-only
triage: anchor
---

# Rosenzweig–Stanfill: logarithmic Laplacians and Bell polynomials

Source: arXiv:2606.04225v1 (2 June 2026), Section 1, Open Problem 1.3,
page 2. The statement is:

> Show that $p_{2m,S_1}(\tfrac{1}{2}-m)\neq0$ for all $m\in\mathbb{N}$ where the sequence $S_1$ satisfies (1.8).

Definition 1.1, page 2:

> Given a sequence of numbers, $S$, indexed over a set $J\supseteq \mathbb{N}$, we define
> $p_{j,S}(t):=\sum_{k=0}^j \frac{(-1)^k}{k!} \widehat{B}_{j,k}(s_1,\dots,s_{j-k+1})t^k=\frac{(-1)^j}{j!}\det\mathcal{N}_{j,S}(t),\quad j\in\mathbb{N}_0,$
> where $\widehat{B}_{n,k}$ denote the partial ordinary Bell polynomials (see Section 1.2) and the $j\times j$ lower Hessenberg matrix $\mathcal{N}_{j,S}(t)$ consists of $s_1 t$ on the diagonal, $(k+1)s_{k+1} t$ on the $k$th subdiagonal, the sequence $1,2,\dots, j-1$ on the first superdiagonal, and zeros on all other superdiagonals (cf. [19, Eq. (5.3)]):

Equation (1.8), page 2:

$$
s_k^{(1)}=(1-2^{1-k})\frac{2 B_{k}}{k}=-\frac{2}{k}B_k(1/2),\quad k\in\mathbb{N}.
$$

Section 1.2, page 5 fixes the convention:

> $B_k$ denotes the Bernoulli numbers with the convention $B_1=-1/2$;

On page 6 it gives the partial ordinary Bell polynomial:

$$
\widehat{B}_{n,k}(z_1,z_2,\dots,z_{n-k+1})=\sum \frac{k!}{j_1!j_2!\dots j_{n-k+1}!}z_1^{j_1} z_2^{j_2} \dots z_{n-k+1}^{j_{n-k+1}},
$$

> with the sum being over all sequences $j_1,j_2,\dots,j_{n-k+1}$ of nonnegative integers such that
> $j_1+j_2+\dots+j_{n-k+1}=k,\quad j_1+2j_2+\dots+(n-k+1)j_{n-k+1}=n.$

The rational definition `pBell` uses the first expression of Definition 1.1;
`bellOrdinary` uses this literal natural-sequence sum. `BellProfile` is the
subtype carrying precisely its two constraints, with zero-based indices.
`S1` uses the first expression of (1.8), with the signed exponent formed in
the integers. Lean's natural numbers include zero, so the source's positive
natural quantifier is encoded as `∀ m : ℕ, 1 ≤ m → …`. No determinant identity
or analytic continuation theorem is claimed by the Lean module.

The proof isolates the profile with `j₂=m`. Multiplication by `24^m m!`
makes that summand have 2-adic valuation zero and all other nonzero summands
have positive valuation. This proves the stated nonvanishing for every
positive natural index. Combining it with the paper's Theorem 1.2 and
residue formula (1.7) removes the qualification “possible” from the poles
of the diagonal fundamental solution at `t=1/2-m`; this analytic consequence
uses the paper's theorem and is not formalized in this module.

Remark 2.7, page 8, relates the Bell values to the even-index constants
`p_{j,S₂(s)}(1-j)`. Formalization of that bridge and of the combined conjecture
involving Open Problem 1.6(i) remains a separate question.

## Verified locator

- DOI: 10.48550/arXiv.2606.04225
- URL: https://arxiv.org/abs/2606.04225
- Version: arXiv:2606.04225v1, 2 June 2026.
- Open Problem 1.3 and equations (1.5), (1.8): page 2.
- Natural-profile Bell formula: Section 1.2, page 6.
- Bernoulli convention: Section 1.2, page 5.
- Related constants: Remark 2.7, page 8.
