---
bibkey: rosenzweigstanfill2026loglaplacians
authors: Bart Rosenzweig and Jonathan Stanfill
year: 2026
title: "On the fundamental solutions of two nonlocal parabolic equations related to logarithmic Laplacians"
doi: 10.48550/arXiv.2606.04225
url: https://arxiv.org/abs/2606.04225v1
claim: "Open Problem 1.6(iv) asks whether expression (1.13) vanishes for every alpha in (0, pi) whenever m is nonnegative and even."
strata_touched:
  - D5/S3/ArithSums/LogLaplacianEvenResidueVanishing
license: citation-only
triage: anchor
---

# Rosenzweig–Stanfill logarithmic Laplacians

## Verified locator

- DOI: 10.48550/arXiv.2606.04225
- URL: https://arxiv.org/abs/2606.04225v1
- Version: arXiv:2606.04225v1.

## Source statement

Open Problem 1.6, printed page 4:

> Consider the notation of Theorem 1.5. Then the following are conjectured to be true:
>
> (iv) For every α ∈ (0, π), (1.13) is equal to zero whenever m ≥ 0 is even.

Definition 1.1, printed page 2:

> Given a sequence of numbers, S, indexed over a set J ⊇ N, we define

$$
p_{j,S}(t):=\sum_{k=0}^{j}\frac{(-1)^k}{k!}\widehat B_{j,k}(s_1,\ldots,s_{j-k+1})t^k,
\qquad j\in\mathbb N_0.
$$

Theorem 1.5, printed page 4:

> where the sequence S₂ satisfies sₖ⁽²⁾ = −Bₖ/k, k ∈ N.

The paper fixes $B_1=-1/2$. Equations (1.20)–(1.21), printed page 6,
define the partial ordinary Bell polynomials by a multinomial sum over
nonnegative profiles with total count $k$ and weighted count $n$.
The formal encoding uses these formulas, the recursive primary $c$-array
of (1.14), its separate value at $\alpha=\pi/2$, and the finite $d$ and $b$
arrays. The zero entry of the positive-index Bell sequence is unused.
The expression (1.13) is $2e^{\gamma_E m}/\pi$ times the two-sum bracket;
this nonzero factor does not affect vanishing.

The settlement concerns clause (iv). Clauses (i)–(iii), the analytic
construction of the fundamental solution, and analytic convergence of
its power series are separate statements.
