---
bibkey: bugujaffe2025ruzsa
authors: Kaifeng Bu; Weichen Gu; Arthur Jaffe
year: 2025
title: "Quantum Ruzsa Divergence to Quantify Magic"
doi: 10.1109/TIT.2025.3543276
url: "https://arxiv.org/abs/2401.14385v3"
claim: "The paper defines a quantum Ruzsa divergence and a quantum-doubling constant through the qudit quantum convolution, proves a quantum inverse sumset theorem for pure states bounding the relative entropy to the mean state by the doubling constant, the rank of the mean state and the magic gap, and expects the analogous bound with a purity factor to hold for mixed states."
strata_touched:
  - D5/S3/Quantum/Magic/MixedStateInverseSumsetRefutation
license: citation-only
triage: anchor
---

# Bu, Gu and Jaffe, Quantum Ruzsa divergence to quantify magic

K. Bu, W. Gu and A. Jaffe, IEEE Transactions on Information Theory 71(4) (2025) 2726–2740, DOI 10.1109/TIT.2025.3543276; arXiv:2401.14385v3. Quotations are from the arXiv v3 TeX source.

For a prime $d$, the convolution of two $n$-qudit states is $\rho\boxtimes_{s,t}\sigma=\operatorname{Tr}_B[U_{s,t}(\rho\otimes\sigma)U_{s,t}^\dagger]$ with $U_{s,t}|\vec i,\vec j\rangle=|s\vec i+t\vec j,\,-t\vec i+s\vec j\rangle$ and $s^2+t^2\equiv1\pmod d$, $s,t\ne0$. The quantum-doubling constant is $\delta_q[\rho]=\exp(S(\rho\boxtimes\rho)-S(\rho))$. The mean state $\mathcal M(\rho)$ keeps the part of the characteristic function of modulus one, $R(\rho)$ is its rank, and $\lambda=(1-MG(\rho))^2$ with the magic gap $MG$. Theorem 44 bounds $D(\psi\|\mathcal M(\psi))$ for pure states $\psi$ with $1<\delta_q[\psi]\le C$ by $\frac{\log R(\psi)}{\log R(\psi)-\log[1+\lambda(R(\psi)-1)]}\log C$. Remark 45 states:

> In addition, we also expect that the property (2) in Theorem 44 holds, which has the following form
> $$D(\rho\|\mathcal M(\rho))\le\frac{\log R(\rho)}{\log R(\rho)-\log[1+\lambda(R(\rho)\operatorname{Tr}[\rho^2]-1)]}\log C.$$

The remark proves only a weaker bound with $\log R(\rho)-S(\rho)$ in numerator and denominator and leaves the expected one "for a future study".

## Verified locator

Source: https://arxiv.org/abs/2401.14385v3
- DOI: https://doi.org/10.1109/TIT.2025.3543276 (journal version; title, authors, journal, volume, issue and pages from Crossref).
- URL: https://arxiv.org/abs/2401.14385v3. The e-print member `IEEE_Final_BGJ.tex` has 2946 lines and md5 `bc35601f976e76a374c2ca4f68d78fea`. Locations:
  - Weyl operators and the characteristic function, l. 726–780;
  - the mean state, l. 842–856; the magic gap, l. 870–876; the convolution, l. 885–896;
  - the rank $R(\rho)$ of the mean state, l. 1000; the quantum-doubling constant, l. 1982–1994;
  - Theorem 44, l. 2026–2037; Remark 45 and the expected mixed-state inequality, l. 2101–2123.
