---
bibkey: siudzinska2020pauligeometry
authors: Katarzyna Siudzińska
year: 2020
title: "Geometry of generalized Pauli channels"
doi: 10.1103/PhysRevA.101.062323
url: https://arxiv.org/abs/2002.04657v2
claim: "The paper studies the geometry of generalized Pauli channels built from mutually unbiased bases, with the Hilbert-Schmidt line and volume elements of their Choi states. For N = d + 1 bases it computes, for d = 2, 3, 4, 5, the volumes of completely positive maps relative to a box of positivity estimates, of channels with nonnegative eigenvalues relative to all channels, and of entanglement-breaking channels relative to those, and conjectures closed formulas for all d."
strata_touched:
  - D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios
license: citation-only
triage: anchor
---

# Siudzińska, Geometry of generalized Pauli channels

K. Siudzińska, arXiv:2002.04657v2 [quant-ph]; Physical Review A 101(6) (2020), 062323. Quotations are from the v2 TeX source.

For $N=d+1$ mutually unbiased bases the channel eigenvalues are $\lambda_1,\dots,\lambda_{d+1}$, with volume element $\mathrm{d}V=\left(\frac{\sqrt{d-1}}{d}\right)^{d+1}\prod_{\alpha=1}^{d+1}\mathrm{d}\lambda_\alpha$. The positivity estimate is

> $$-\frac{1}{d-1}\leq\lambda_\alpha\leq 1.$$

Appendix A gives the complete positivity region:

> $$-\frac{1}{d-1}\leq\sum_{\alpha=1}^{d+1}\lambda_\alpha\leq 1+d\min_\alpha\lambda_\alpha.$$

The paper defines the channels with $\lambda_\alpha\ge0$ as those "achievable with the time-local generators", with volume $V_G(d)$, and states:

> If $\lambda_\alpha\geq 0$, then $\sum_{\alpha=1}^{d+1}\lambda_\alpha\leq 1$ is the necessary and sufficient condition for breaking the entanglement

After exact computations for $d=2,3,4,5$ it states three conjectures:

> and conjecture that the general formula reads
> $$\frac{V_{CP}(d)}{V_P(d)}=\frac{d}{(d+1)!}.$$

> and conjecture that the general formula reads
> $$\frac{V_{G}(d)}{V_{CP}(d)}=\frac{d^2-1}{d^2}\left(\frac{d-1}{d}\right)^{d}.$$

> from which we conjecture that
> $$\frac{V_{EB}(d)}{V_{G}(d)}=\frac{1}{d+1}.$$

## Verified locator

Source: https://arxiv.org/abs/2002.04657v2
- DOI: https://doi.org/10.1103/PhysRevA.101.062323 (Physical Review A 101(6), 062323; published 18 June 2020; title, author, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2002.04657v2. The e-print is a gzipped tar archive; its member `GGPC_volume5.tex` has 569 lines and md5 `fd8c2bae5bceeba366de934044c2363f`. Locations:
  - Section "Relative volumes of quantum channels", l. 180; the positivity estimate and $V_P(d)$, l. 210–228;
  - Subsection "$N=d+1$ and $N=d$ mutually unbiased bases", l. 231; the three conjectures, l. 243–246, l. 276–280, l. 302–305;
  - Appendix A, l. 359–364.
- The arXiv record lists v1 (11 February 2020) and v2 (15 April 2020), with the journal reference "Phys. Rev. A 101, 062323 (2020)" (arXiv API metadata).
