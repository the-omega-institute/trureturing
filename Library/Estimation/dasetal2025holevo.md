---
bibkey: dasetal2025holevo
authors: Das, Aritra; Conlon, Lorcán O.; Suzuki, Jun; Yung, Simon K.; Lam, Ping K.; Assad, Syed M.
year: 2025
title: "Holevo Cramér-Rao bound: How close can we get without entangling measurements?"
doi: 10.22331/q-2025-09-30-1867
url: "https://arxiv.org/abs/2405.09622v2"
claim: "The paper compares the Holevo Cramér-Rao bound (collective measurements) with the Nagaoka-Hayashi Cramér-Rao bound (separable measurements) in multiparameter estimation, proves that their ratio is at most n for n parameters and at most d+2 for full orthonormal-basis tomography of a d-dimensional state, shows the value d+1 at the maximally mixed state, and proposes that the ratio for the linear generalized Gell-Mann model is at most d+1."
strata_touched:
  - D5/S3/Quantum/Measurements/OnbTomographyHolevoRatio
license: citation-only
triage: anchor
---

# Das et al., Holevo Cramér-Rao bound: How close can we get without entangling measurements?

A. Das, L. O. Conlon, J. Suzuki, S. K. Yung, P. K. Lam and S. M. Assad, Quantum 9, 1867 (2025), DOI 10.22331/q-2025-09-30-1867; arXiv:2405.09622v2 (25 September 2025). Quotations are from the arXiv v2 TeX source `DraftQuantumSubmission.tex`; macros are expanded.

For locally unbiased Hermitian operators $X_1,\dots,X_n$ ($\operatorname{tr}(\rho_\theta X_j)=\theta_j$, $\operatorname{tr}(\partial_j\rho_\theta X_k)=\delta_{jk}$), the HCRB is $\min_{\mathbb X}\{\operatorname{tr}\mathbb Z_\theta[\mathbb X]+\|\operatorname{Im}\mathbb Z_\theta[\mathbb X]\|_1\}-\operatorname{tr}(\theta\theta^\top)$ with $\mathbb Z_\theta[\mathbb X]_{jk}=\operatorname{tr}(\rho_\theta X_jX_k)$ (l. 658–666), and the NHCRB is $\min_{\mathbb L,\mathbb X}\{\mathbb{T}\mathrm r[\mathbb S_\theta\mathbb L]\mid\mathbb L\succcurlyeq\mathbb X\mathbb X^\top,\ \mathbb L_{jk}=\mathbb L_{kj}\ \text{Hermitian}\}-\operatorname{tr}(\theta\theta^\top)$ with $\mathbb S_\theta=\mathbb 1_n\otimes\rho_\theta$ (l. 588–602). The collective enhancement is $\mathcal R^{\mathrm{NH}}=\max_\theta\mathrm C_{\mathrm{NHCRB}}/\mathrm C_{\mathrm{HCRB}}$ (l. 798–801). For the linear model $\rho_\theta=\mathbb 1_d/d+\sum_{j=1}^{d^2-1}\theta_j\lambda_j$ with $\operatorname{Tr}(\lambda_j\lambda_k)=\delta_{jk}$, the paper proves $\mathcal R^{\mathrm{NH}}\le d+2$ and states (l. 1147–1155):

> Although we prove an upper bound of $d+2$, based on numerical evidence shown in Fig. 3, we expect the attainable bound to be $d+1$ and expect $\mathcal{R}^{\mathrm{NH}}[\{\rho_\theta\}]$ to be maximised at $\theta=0$ over $\Theta$. Thus for the linear GMM model, we propose $\mathcal{R}^{\mathrm{NH}}[\{\rho_\theta\}]\leq d+1$.

## Verified locator

- DOI: https://doi.org/10.22331/q-2025-09-30-1867
- Source: https://arxiv.org/abs/2405.09622v2
