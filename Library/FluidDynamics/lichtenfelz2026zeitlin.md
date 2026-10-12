---
bibkey: lichtenfelz2026zeitlin
authors: Leandro Lichtenfelz, Klas Modin, Stephen C. Preston
year: 2026
title: "Ricci curvature for hydrodynamics on the sphere"
doi: 10.1007/s00220-025-05533-w
url: https://arxiv.org/abs/2508.09833v1
claim: "Conjecture 1 states the four spin-weighted Wigner six-j identities (2.10)-(2.13); their validity supplies the hypothesis of Theorem 3. Conjecture 2 states that for each fixed l > 1 the averaged Ricci curvature of the Zeitlin metric on SU(N) becomes negative for large N and tends to -(H_l - 1)/2."
strata_touched:
  - D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah
  - D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules
  - D5/S3/Quantum/Algebra/ZeitlinSixJ/RicciLimit
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

The Ricci curvature components (eq. (2.4), `eq_ricci_intro`):

> $r_{\ell}(N)^+ := \frac{N}{\hbar_N^2} \sum\limits_{\substack{k, k' = 1 \\ k+k'+\ell\;\mathrm{odd}}}^{N-1} \frac{\lambda_{\ell}}{\lambda_{k}\lambda_{k'} } \, (2k+1)(2k'+1) \left\{\begin{matrix} \ell & k & k' \\ \frac{N-1}{2} & \frac{N-1}{2} & \frac{N-1}{2} \end{matrix} \right\}^2$, $r_{\ell}(N)^- := \frac{N}{\hbar_N^2} \sum\limits_{\substack{k, k' = 1 \\ k+k'+\ell \;\mathrm{odd}}}^{N-1} \frac{ (\lambda_{k}-\lambda_{k'})^2}{\lambda_{k}\lambda_{k'}\lambda_{\ell}} \, (2k+1)(2k'+1) \left\{\begin{matrix} \ell & k & k' \\ \frac{N-1}{2} & \frac{N-1}{2} & \frac{N-1}{2} \end{matrix} \right\}^2.$ Here, $\lambda_i = i(i+1)$, $\hbar_N = 2/\sqrt{N^2-1}$ and $\{:::\}$ denotes the Wigner $6j$ symbol.

Theorem 3 (`theorem_3`): "Assuming the identities in Conjecture 1, the positive and negative parts of the Ricci curvature in the $V_{\ell}$ subspace satisfy: $r_{\ell}(N)^- = \frac{2(H_{\ell}-1)}{\hbar_N^2} = 2(H_{\ell}-1)\left(\frac{N^2-1}{4}\right)$, $r_{\ell}(N)^+ \leq (4H_{\ell} + 2\ell+1) \left(\frac{N^2-1}{4}\right)$."

Averaged curvature (eq. (2.15)): "$\widetilde{r}_{\ell}(N) = \frac{r_{\ell}(N)}{N^2-1}, \qquad \widetilde{r}_{\ell}(N)^{\pm} = \frac{r_{\ell}(N)^{\pm}}{N^2-1}$."

Conjecture 2 (`conjecture_ricci`, eq. (2.16)): "For each fixed $\ell > 1$, the averaged Ricci curvature $\widetilde{r}_{\ell}(N)$ of the Zeitlin metric on $SU(N)$ becomes negative for sufficiently large $N$, and in the limit $\widetilde{r}_{\ell}(N) \rightarrow -\frac{H_{\ell}-1}{2}$, as $N \rightarrow \infty$, where $H_{\ell}$ is the $\ell^{\text{th}}$ harmonic number."

The source continues: "Once these identities are proved, the asymptotic behavior in Conjecture 2 would follow by deriving a sharper upper bound for $r_{\ell}(N)^+$ in order to prove that $\lim_{N\to\infty} \tilde{r}_{\ell}(N)^+=0$ for each $\ell$."

Remark after the upper bound (`eq_6j_upper_bound`): "On the other hand, if $i+j+\ell$ is \emph{odd}, then the coefficients $C^{\ell 0}_{i0j0}$ vanish and the proof of (`eq_clebschgordan`) given in [Brussaard–Tolhoek] is no longer valid. Indeed, numerically it seems that a sharper bound than (`eq_6j_upper_bound`) is possible in the case of $i+j+\ell$ odd, which would help with Conjecture 2, but this requires exploiting this parity assumption somehow."

## Verified locator

- arXiv version: https://arxiv.org/abs/2508.09833v1
- Source: `Ricci_Block.tex`, `conj_new_formulas`, equations (2.10)-(2.13).
- Source: `Ricci_Block.tex`, `eq_ricci_intro` (2.4), `theorem_3`, (2.15) and `conjecture_ricci` (2.16).
- Journal: Communications in Mathematical Physics 407 (2026), article 37,
  https://doi.org/10.1007/s00220-025-05533-w.
- Racah definition: https://dlmf.nist.gov/34.4.E2.
- Recurrences and symmetries: https://dlmf.nist.gov/34.5.

The arXiv text and its TeX source are the quoted version. The journal text
has not been compared sentence by sentence with it.
