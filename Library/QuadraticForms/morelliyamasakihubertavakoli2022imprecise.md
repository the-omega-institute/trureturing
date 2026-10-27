---
bibkey: morelliyamasakihubertavakoli2022imprecise
authors: Simon Morelli; Hayata Yamasaki; Marcus Huber; Armin Tavakoli
year: 2022
title: "Entanglement detection with imprecise measurements"
doi: 10.1103/PhysRevLett.128.250501
url: https://arxiv.org/abs/2202.13131v2
claim: "The paper bounds entanglement witnesses when lab measurements deviate from the targets by a fidelity-based inaccuracy epsilon; for the CHSH witness with targets sigma_X and sigma_Z on two qubits it gives an explicit separable model attaining 4(1-2eps)sqrt(eps(1-eps)) + sqrt(2-16eps(1-eps)(1-2eps)^2) for eps up to 1/2-1/(2 sqrt 2) and 2 beyond, and conjectures that this model is optimal."
strata_touched:
  - D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum
license: citation-only
triage: anchor
---

# Morelli, Yamasaki, Huber and Tavakoli, entanglement detection with imprecise measurements

S. Morelli, H. Yamasaki, M. Huber and A. Tavakoli, arXiv:2202.13131v2 [quant-ph] (15 May 2022; v1 26 February 2022); Phys. Rev. Lett. 128, 250501 (2022). Quotations are from the v2 TeX source, with the macros `\Tr`, `\expect`, `\norm` written out and cross-references omitted.

The two-outcome inaccuracy constraint, for lab observables $A_x=A_{1|x}-A_{2|x}$ and targets $\tilde A_x$:

> $\operatorname{Tr}\left(A_{x}\tilde{A}_{x}\right)\geq d\left(1-2\varepsilon^\text{A}_x\right)$, $\operatorname{Tr}\left(B_{y}\tilde{B}_{y}\right)\geq d\left(1-2\varepsilon^\text{B}_y\right)$ … The observables can be arbitrary Hermitian operators whose extremal eigenvalue is bounded by unity, i.e. $\|A_x\|_\infty\leq 1$ and $\|B_y\|_\infty\leq 1$.

The CHSH witness and the conjecture (main text):

> consider the CHSH quantity for entanglement detection, namely $\mathcal{W}=\langle\sigma_X\otimes \left(\sigma_X+\sigma_Z\right)\rangle+\langle\sigma_Z\otimes \left(\sigma_X-\sigma_Z\right)\rangle$. … However, as we show in Supplementary Material through an explicit separable model that we conjecture to be optimal, this fact does not qualitatively improve the robustness of idealised ($\varepsilon=0$) entanglement detection to small inaccuracies. We obtain $\mathcal{W}_\text{sep}=4\left(1-2\varepsilon\right)\sqrt{\varepsilon(1-\varepsilon)}+\sqrt{2-16\varepsilon\left(1-\varepsilon\right)\left(1-2\varepsilon\right)^2}$, when $\varepsilon\leq \frac{1}{2}-\frac{1}{2\sqrt{2}}$ and $\mathcal{W}_\text{sep}=2$ otherwise.

The supplementary model (Section `AppCHSH`) takes $A_1=B_1$, $A_2=B_2$ with Bloch vectors in the $XZ$-plane at angles $\alpha=\arccos(1-2\varepsilon)$, $\beta=\arcsin(1-2\varepsilon)$, and a product state $|\phi\rangle\otimes|\phi\rangle$.

## Verified locator

Source: https://arxiv.org/abs/2202.13131v2
- DOI: https://doi.org/10.1103/PhysRevLett.128.250501 (Phys. Rev. Lett. 128, 250501 (2022); author list, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2202.13131v2 (the e-print is a gzipped tar archive; member `Manuscript_epsilonEW.tex`, 405 lines, md5 `cd8e9557361d4082b54a066c0a876cce`):
  - the framework, the fidelity constraint and the two-outcome observables, l. 77–100;
  - the CHSH witness, the conjecture and the separable value, l. 111–118;
  - the explicit separable model, Section `AppCHSH`, l. 232–257.
- The author list and the arXiv dates are from the arXiv metadata.
