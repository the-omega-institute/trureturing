---
bibkey: lichtenfelz2026zeitlin
authors: Leandro Lichtenfelz, Klas Modin, Stephen C. Preston
year: 2026
title: "Ricci curvature for hydrodynamics on the sphere"
doi: 10.1007/s00220-025-05533-w
url: https://arxiv.org/abs/2508.09833v1
claim: "Conjecture 1 states the four spin-weighted Wigner six-j identities (2.10)-(2.13); their validity supplies the hypothesis of Theorem 3."
strata_touched:
  - D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah
  - D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules
license: citation-only
triage: anchor
---

# Ricci curvature for hydrodynamics on the sphere

Lichtenfelz, Modin and Preston study the Ricci curvature of the Zeitlin
approximation to incompressible hydrodynamics on the sphere. Their
Conjecture 1 appears on page 6 of arXiv:2508.09833v1, section 2.2.
The following quotation retains its four displayed identities:

> For all $1 \leq j, \ell \leq N-1$, we have

$$
\begin{aligned}
\sum\limits_{i = 1}^{N-1} \frac{(2i+1)}{\lambda_{i}}
(\mathcal{W}^{ij\ell})^2 &= \frac{1}{N|j - \ell|(j + \ell + 1)}, \qquad (j\neq \ell),  \\
\sum\limits_{i = 1}^{N-1} (-1)^{i} \lambda_{i}(2i+1)
(\mathcal{W}^{ij\ell})^2 &=(-1)^{N+1}(\lambda_j + \lambda_{\ell})\mathcal{W}_j^{\ell},  \\
\sum\limits_{i = 1}^{N-1} \lambda_{i}(2i+1)
(\mathcal{W}^{ij\ell})^2 &= \frac{(N^2-1)\big(\lambda_j+\lambda_{\ell}\big) - 2\lambda_j\lambda_{\ell}}{N(N^2-1)},  \\
\sum\limits_{i = 1}^{N-1}\frac{2i+1}{\lambda_i}\left(\frac{1}{N} + (-1)^{i+j+N}\mathcal{W}_j^i\right) &= \frac{2H_j}{N},
\end{aligned}
$$

> where $\lambda_i = i(i+1)$ as before and $H_j = 1 + 1/2 + \cdots + 1/j$ is the $j^{\text{th}}$ harmonic number.

> To begin, for fixed $N$, we introduce the abbreviated notation below for certain $6j$ symbols that appear frequently throughout the paper:

$$
\mathcal{W}^{ij\ell} = \left\{\begin{matrix}i&j&\ell\\\frac{N-1}{2}&\frac{N-1}{2}&\frac{N-1}{2}\end{matrix}\right\},\qquad
\mathcal{W}_j^i = \left\{\begin{matrix}i&\frac{N-1}{2}&\frac{N-1}{2}\\j&\frac{N-1}{2}&\frac{N-1}{2}\end{matrix}\right\}.
$$

Here $\mathcal W^{ij\ell}$ has top row $i,j,\ell$ and bottom row
$(N-1)/2,(N-1)/2,(N-1)/2$; $\mathcal W_j^i$ has top row
$i,(N-1)/2,(N-1)/2$ and bottom row $j,(N-1)/2,(N-1)/2$.
The symbol is the standard Wigner six-j symbol. The finite Racah formula
and its triangle coefficient are DLMF 34.4.2; their summation offsets are
ordinary integral spins. Natural labels in the Lean definition are twice
the corresponding spin, and inadmissible symbols are zero.

The claim is the conjunction of all four identities, for every natural
$N\geq2$. Only (2.10) requires $j\neq\ell$. The shifted index in
$\operatorname{range}(N-1)$ visits exactly $1,\ldots,N-1$.
The harmonic number is rational and is cast to the real numbers.

The paper's Theorem 3 is explicitly conditional on Conjecture 1. The four
identities remove that hypothesis from the paper's Ricci-curvature
argument. The asymptotic Conjecture 2 additionally requires a sharper
upper bound for the positive Ricci contribution; it is a separate question.

## Verified locator

- arXiv version: https://arxiv.org/abs/2508.09833v1
- Source: `Ricci_Block.tex`, `conj_new_formulas`, equations (2.10)-(2.13).
- Journal: Communications in Mathematical Physics 407 (2026), article 37,
  https://doi.org/10.1007/s00220-025-05533-w.
- Racah definition: https://dlmf.nist.gov/34.4.E2.
- Recurrences and symmetries: https://dlmf.nist.gov/34.5.

The arXiv text and its TeX source are the quoted version. The journal text
has not been compared sentence by sentence with it.
