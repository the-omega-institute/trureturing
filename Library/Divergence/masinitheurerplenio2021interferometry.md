---
bibkey: masinitheurerplenio2021interferometry
authors: Michele Masini; Thomas Theurer; Martin B. Plenio
year: 2021
title: "Coherence of operations and interferometry"
doi: 10.1103/PhysRevA.103.042426
url: https://arxiv.org/abs/2102.04863v2
claim: "The paper defines dynamical coherence measures from discrimination games in multi-path interferometers: pre-processed improvements for the ability of an operation to detect coherence and post-processed improvements N for its ability to create coherence, optimized over maximally incoherent operations; it proves that the pre-processed improvements are faithful exactly for unbiased priors and that the post-processed improvements are faithful for unbiased priors, and leaves open whether analogous results hold for the post-processed improvements."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful
license: citation-only
triage: anchor
---

# Masini, Theurer and Plenio, coherence of operations and interferometry

M. Masini, T. Theurer and M. B. Plenio, arXiv:2102.04863v2 [quant-ph] (18 May 2021; v1 9 February 2021); Phys. Rev. A 103, 042426 (2021). Quotations are from the v2 TeX source, with cross-references omitted.

Free operations (Section II A): the maximally incoherent operations are the channels $\Psi$ with

> $\Psi\Delta=\Delta\Psi\Delta$,

where $\Delta$ is the full dephasing in the incoherent basis, and a measure is faithful if $M(\Theta)=0$ exactly if $\Theta$ is a free channel. The phases act as $\Lambda_{\vec\phi}(\sigma)=\sum_{i,j}e^{i(\phi_i-\phi_j)}|i\rangle\langle i|\sigma|j\rangle\langle j|$ on $M$ paths, the prior is $\lambda=1-\mu$, and $\|\cdot\|_1$ on operations is the induced trace norm. The post-processed improvements (Section III B) are

> $N_{\lambda,\vec{\phi}}(\Theta):=\max_{\Psi\in\mathcal{MIO}}\left|\left|\left(\lambda-\mu \Lambda_{\vec{\phi}}\right) \Psi \Theta\Delta\right|\right|_1-|\lambda-\mu |$.

The pre-processed improvements are faithful if and only if $\lambda=\frac12$ (Theorem 2), and $N_{\frac12,\vec\phi}$ is faithful (Theorem 5). The question (Section IV):

> Whilst we provided a method to compute the pre-processed improvements and showed that they are not faithful for $\lambda\ne\mu$, it is an open question whether there exist analogous results for the post-processed cases.

## Verified locator

Source: https://arxiv.org/abs/2102.04863v2
- DOI: https://doi.org/10.1103/PhysRevA.103.042426 (Phys. Rev. A 103, 042426 (2021); author list, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2102.04863v2 (the e-print is a gzipped tar archive; member `PaperMasiniTheurerPlenio.tex`, 2175 lines, md5 `f61fbd9088afa2757500af0fecbe8477`):
  - incoherent states and the dephasing, l. 115;
  - maximally incoherent operations, l. 132–134;
  - faithfulness, l. 153;
  - the phase channel, l. 171–174;
  - Theorem 2, l. 247–249;
  - the post-processed improvements, Eq. (14), l. 273;
  - Theorem 5, l. 286–288;
  - the question, l. 300.
- The author list and the arXiv version dates are from the arXiv metadata.
