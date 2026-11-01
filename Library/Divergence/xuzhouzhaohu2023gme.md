---
bibkey: xuzhouzhaohu2023gme
authors: Xin-Yu Xu; Qing Zhou; Shuai Zhao; Shu-Ming Hu; Li Li; Nai-Le Liu; Kai Chen
year: 2023
title: "General framework for genuine multipartite entanglement detection"
doi: 10.1103/PhysRevA.107.052405
url: "https://arxiv.org/abs/2211.05563v1"
claim: "The paper constructs genuine multipartite entanglement witnesses from bipartite witnesses, gives for noisy n-qudit GHZ states a witness finer than the fidelity witness, derives from it a lower bound on the geometric measure of genuine multipartite entanglement by the Legendre-transform method, and leaves open whether this lower bound equals the geometric measure."
strata_touched:
  - D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap
license: citation-only
triage: anchor
---

# Xu, Zhou, Zhao, Hu, Li, Liu and Chen, General framework for genuine multipartite entanglement detection

X.-Y. Xu, Q. Zhou, S. Zhao, S.-M. Hu, L. Li, N.-L. Liu and K. Chen, Physical Review A 107(5) (2023) 052405, DOI 10.1103/PhysRevA.107.052405; arXiv:2211.05563v1 (titled "A generic framework for genuine multipartite entanglement detection"). Quotations are from the arXiv v1 TeX source.

For noisy GHZ states $\rho_{n,d}(p)=pI/d^n+(1-p)|GHZ_n^d\rangle\langle GHZ_n^d|$ the paper uses the geometric measure $E_G(|\psi\rangle)=1-\max_{|\phi_{bs}\rangle}|\langle\phi_{bs}|\psi\rangle|^2$ over pure biseparable states, extended to mixed states by the convex roof. From the witness $\mathcal W_{o,|GHZ_n^d\rangle}$ (the GHZ projector subtracted from $1/d$ times the projector onto words using at most two distinct symbols) and its expectation $w_{n,d}(p)$ it derives $E_G(\rho_{n,d}(p))\ge\epsilon_o^{n,d}(p)=\sup_r\{r\,w_{n,d}(p)-\hat E_G(r\mathcal W)\}$, with $\hat E_G(r\mathcal W)=\sup_{\psi,\phi_{bs}}\{\langle\psi|(r\mathcal W+|\phi_{bs}\rangle\langle\phi_{bs}|)|\psi\rangle-1\}$, and states:

> It remains open whether $\epsilon_o^{n,d}(p)$ equals $E_G(\rho_{n,d}(p))$.

## Verified locator

Source: https://arxiv.org/abs/2211.05563v1
- DOI: https://doi.org/10.1103/PhysRevA.107.052405 (journal version; title, authors, journal, volume, issue and article number from Crossref; the journal text was not read).
- URL: https://arxiv.org/abs/2211.05563v1. The e-print member `GMEwitness.tex` has 747 lines and md5 `e5fc01c6d6faa619a2bc9e11d7a16bb1`. Locations:
  - the section on estimating entanglement measures, l. 247–312, with the noisy GHZ family, the geometric measure and its convex roof, $\epsilon_o$ and $\hat E_G$ at l. 284–311;
  - the open question, l. 325;
  - the witness for states admitting a Schmidt decomposition and its orthogonal set, l. 682–700.
