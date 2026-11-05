---
bibkey: sudmarshallwangrieffelwudarski2022dual
authors: James Sud; Jeffrey Marshall; Zhihui Wang; Eleanor Rieffel; Filip A. Wudarski
year: 2022
title: "Dual-map framework for noise characterization of quantum computers"
doi: 10.1103/PhysRevA.106.012606
url: https://arxiv.org/abs/2112.04414v1
claim: "The paper introduces a dual-map framework for noisy expectation values, defines the marginal approximation to the effective noise (MATEN) as the tensor product of the single-qubit marginals of the noise channel, evaluates it on QAOA circuits and on Rigetti hardware, computes that the maximally entangled process matrix gives fidelity 4^-N with its marginal approximation, and conjectures that this process matrix is the worst case for the MATEN protocol."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity
license: citation-only
triage: anchor
---

# Dual-map framework for noise characterization of quantum computers

J. Sud, J. Marshall, Z. Wang, E. Rieffel and F. A. Wudarski, arXiv:2112.04414v1; Phys. Rev. A 106, 012606 (2022). Quotations are from the v1 TeX source.

The marginal approximation:

> we define a marginal approximation to the effective noise (MATEN) as $\tilde{\ep} = \bigotimes_{k=1}^N \tr_{\bar{k}}\left(\ep\right) = \bigotimes_{k=1}^N \ep_k,$ where $\tr_{\bar{k}}(\ep) = \ep_k$ traces out all subsystem except $k$-th

The process matrix:

> $\mathcal{E}_\chi(\rho) = \sum_{k,l=0}^3 \chi_{kl}\sigma_k \rho \sigma_l,$ where $\chi_{kl}$ are elements of the $\chi$ matrix

The maximally entangled process matrix and the conjecture:

> $\chi = \ket{\Psi}\bra{\Psi} \to \chi_{\mathrm{MA}} =\bigotimes_{k=1}^N \left(\frac{1}{4}\mathbbm{1} \right) = \frac{1}{4^N}\mathbbm{1}_{4^N},$ [...] Above we denote the non-local process matrix $\chi$ as the maximally entangled state, that is defined as a projector onto $\ket{\Psi}=\frac{1}{2}\sum_{i=0}^3\ket{ii\ldots i}$, with $N$ 4D subsystems (each corresponding to a qubit), note that this is a GHZ state \cite{greenberger2007going}. We conjecture that the effective channel with the maximally entangled $\chi$ matrix is the worst case scenario for the proposed MATEN protocol.

> However, this conjecture requires more rigorous treatment, which we leave as an open problem. Note that maximally entangled $\chi$ is a completely valid choice, since $\chi\ge0$ and the map associated with it is trace preserving.

The fidelity:

> $F\left(\chi, \chi_{MA}\right) = \frac{1}{4^{N}}\tr(\sqrt{\chi})^2=\frac{1}{4^N},$

## Verified locator

Source: https://arxiv.org/abs/2112.04414v1
- URL: https://arxiv.org/abs/2112.04414v1 (source `main.tex`, md5 `b2275e7db7e3a63cc4c871c172f7943a`):
  - the marginal approximation, l. 226–232;
  - the process matrix, l. 234–237;
  - the maximally entangled process matrix and the conjecture, l. 284–290;
  - the fidelity, l. 292–296.
- DOI: 10.1103/PhysRevA.106.012606 (https://doi.org/10.1103/PhysRevA.106.012606).
