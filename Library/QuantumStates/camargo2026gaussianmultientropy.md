---
bibkey: camargo2026gaussianmultientropy
authors: H. A. Camargo, M. Nishida
year: 2026
title: "Genuine Multi-Entropy of Fully Symmetric Gaussian States"
doi: 10.48550/arXiv.2609.30754
url: https://arxiv.org/abs/2609.30754v1
claim: "For fully symmetric pure Gaussian states with diagonal a ≥ 1, the tripartite genuine Rényi multi-entropy is conjectured to satisfy GM^{(3)}_n ∼ ((2−n)/(2n)) log a as a → ∞ for every replica index n and every number of modes N; GM^{(3)}_2 = 0 is proved for every pure bosonic Gaussian state."
strata_touched:
  - D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic
license: citation-only
triage: anchor
---

# Camargo and Nishida, genuine multi-entropy of fully symmetric Gaussian states

H. A. Camargo and M. Nishida, *Genuine Multi-Entropy of Fully Symmetric Gaussian States*,
arXiv:2609.30754v1 (25 September 2026; hep-th, cross-listed quant-ph and cond-mat.stat-mech).

## Verified locator

DOI: 10.48550/arXiv.2609.30754.
Primary version: https://arxiv.org/abs/2609.30754v1 (the only arXiv version).
The TeX source `draftv1.tex` of v1 supplies §2.1 (the multi-entropy, the twists $g_A,g_B,g_C$,
the replica contraction and the genuine multi-entropy), §2.3 (the pure Gaussian state and its
density kernel), §3.1 (the fully symmetric state and its off-diagonal entry), §3.2 (Table 1 and the
conjecture, Eq. (3.8), label `AsymB`) and §4 (the proof of $\mathrm{GM}^{(3)}_2=0$).

## Source statements

Multi-entropy (§2.1): "$S^{(\mathtt{q})}_n(A_1:A_2:\dots:A_\mathtt{q}) := \frac{1}{1-n}\frac{1}{n^{\mathtt{q}-2}}\log \frac{Z^{(\mathtt{q})}_n}{(Z^{(\mathtt{q})}_1)^{n^{\mathtt{q}-1}}}$",
with, for $\mathtt q=3$, "$g_{A}=(1,2,\dots,n)(n+1,n+2,\dots,2n)\cdots(n^2-n+1,n^2-n+2,\dots, n^2)$",
"$g_{B}=(1,n+1,\dots,n^2-n+1)(2,n+2,\dots,n^2-n+2)\cdots(n,2n,\dots, n^2)$", "$g_{C}=(1)(2)\cdots(n^2)$",
and "$Z^{(\mathtt{3})}_n=\prod_{i=1}^{n^2}\delta^{\alpha_{g_A(i)}}_{\alpha'_i}\delta^{\beta_{g_B(i)}}_{\beta'_i}\delta^{\gamma_{g_C(i)}}_{\gamma'_i}\prod_{j=1}^{n^2} \rho_{\alpha_j\beta_j\gamma_j}^{\alpha'_j\beta'_j\gamma'_j}$".

Genuine multi-entropy (§2.1): "$\text{GM}^{(\mathtt{3})}_n(A:B:C) :=S^{(\mathtt{3})}_n(A:B:C) -\frac{1}{2}\left(S_n^{(\mathtt{2})}(AB:C)+S_n^{(\mathtt{2})}(BC:A)+S_n^{(\mathtt{2})}(CA:B)\right)$".

Gaussian kernel (§2.3): "$\rho(\mathbf{q},\mathbf{q}') =\left(\det\left(\frac{\mathbf{R}}{\pi}\right)\right)^{1/2} \exp\left[-\frac{1}{2}\left(\mathbf{q}^\top\cdot \mathbf{W}\cdot \mathbf{q}+{\mathbf{q}'}^\top\cdot \mathbf{W}^*\cdot \mathbf{q}'\right)\right]$".

Fully symmetric state (§3.1): "all diagonal elements are $a\ge1$ and all off-diagonal elements are $e^-$, where
$e^-:=\frac{(a^2-1)(N-2)-\sqrt{a^2-1} \sqrt{(a^2-1)N^2+4(N-1)}}{2 a (N-1)}$".

Conjecture (§3.2, Eq. (3.8)): "$\text{GM}^{(\mathtt{3})}_n\sim \frac{2-n}{2n}\log a \;\;\;(a\to\infty)$ …
we \emph{conjecture} that the asymptotic behavior \eqref{AsymB} is valid for the fully symmetric
Gaussian states with any $n$ and $N$."

## Scope

The paper derives Eq. (3.8) from exact formulas for $N\le8$ and $n\le4$ (Table 1) and proves
$\mathrm{GM}^{(3)}_2=0$ for every pure bosonic Gaussian state (§4). The fully symmetric states
have real $\mathbf W$.
