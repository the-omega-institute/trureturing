---
bibkey: ahiablekothakondawinter2026geometry
authors: Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter
year: 2026
title: "The geometry of absolute separability and other convex matrix properties from spectrum"
doi: 10.48550/arXiv.2608.03390
url: https://arxiv.org/abs/2608.03390v2
claim: "Conjecture 6.7 states equality of APPT maximum purity and the inscribed polytope maximum, with the spectra of equation (44)."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2608.03390

Source: https://arxiv.org/abs/2608.03390v2

## Conjecture 6.7

Page 29, verbatim statement (equation reference rendered as its printed number):

Let $\mathcal P_{m,n}\subseteq \mathrm{APPT}_{m,n}$ be the inscribed absolute PPT polytope with $2\leq m\leq n,\; n>2$. Then
$$
      \max_{\lambda\in \mathrm{APPT}_{m,n}}
    \sum_{i=1}^{mn}\lambda_i^2=  \max_{\lambda\in\mathcal P_{m,n}}
    \sum_{i=1}^{mn}\lambda_i^2
$$
and occurs at the spectra given by Eq. (44).

## Inscribed-polytope maximum

Corollary 6.4, pages 26–27, verbatim source statement:

Let $\mathcal P_{m,n}\subseteq \mathrm{APPT}_{m,n}$ be the inscribed absolute PPT polytope with $2\leq m\leq n,\; n>2$. The maximum achievable purity of a quantum state $\rho \in \mathcal{M}_m \otimes \mathcal{M}_n$ with spectrum $\lambda \in \mathcal P_{m,n}$ is given by
$$
    \max_{\lambda\in\mathcal P_{m,n}}
    \sum_{i=1}^{mn}\lambda_i^2=
    \begin{cases}
    \displaystyle
    \frac{mn+8}{(mn+2)^2},&\textrm{if }  n<n^*, \\[2ex]
    \displaystyle
    \frac{m}{(m^2-1)n},&\quad n\geq n^* \text{ and } \big(m \text{ is odd or } n \text{ is even}\big), \\[2ex]
    \displaystyle
    \frac{mn(m^2-1)+2m}{
    \big((m^2-1)n+1\big)^2},
    &\quad n\geq n^*,\ m \text{ is even and } n \text{ is odd }
    \end{cases}$$ where $$n^* = \frac{2(m^2-2) + 2\sqrt{(m^2-1)(m^2-4)}}{m}.$$
Furthermore, the spectrum of the maximal purity state with $\lambda_1 \geq\cdots\geq \lambda_{mn}\geq 0$ is given by
$$
    \begin{cases}
      \lambda_1 =\frac{3}{mn+2} , \quad \lambda_j = \frac{1}{mn+2} &\text{for } j = 2,\ldots, mn,\  \qquad \qquad \qquad \qquad \quad \;\text{ if } n < n^* \\
      \lambda_i =a , \quad \lambda_j =b &\text{for } i = 1,\ldots, t \ \text{ and } \ j = t + 1, \ldots, mn, \ \text{ if } n \geq n^*
    \end{cases}
$$
where the block size $t = \left\lceil \frac{(m-1)n}{2} \right\rceil$, and the eigenvalues $a$ and $b$ evaluate exactly to
$$
    a = \frac{m+1}{2t + mn(m-1)} \quad \text{and} \quad b = \frac{m-1}{2t + mn(m-1)}.
$$

## Partial transpose convention

Page 2:

> $\Gamma(X \otimes Y) = X \otimes Y^T$, where $X \in \mathcal M_m$ and $Y \in \mathcal M_n$, and $T$ denotes the standard matrix transpose.

## Absolute PPT convention

Page 2:

> Defined analogously to absolutely separable states, absolute PPT states are those states which remain PPT after global unitary rotations and have been completely characterized across all dimensions [17].

Page 11:

> Suppose $\lambda$ is the spectrum of a bipartite state. Then $\lambda\in \mathrm{APPT}_{m,n}$ if and only if for all unitaries $U\in \mathcal{U}(mn)$, $(U\diag(\lambda)U^\dagger)^\Gamma \geq 0$.

The matrix encoding uses the second-factor partial transpose on `Fin 3 × Fin n`. Its trace-squared purity is the real part of `Matrix.trace (rho * rho)`. The qutrit sector substitutes m = 3 and t = n in Corollary 6.4. The two candidate purities become (3n + 8)/(3n + 2)^2 and 3/(8n).
