---
bibkey: songli2022dequantumness
authors: Hongting Song; Nan Li
year: 2022
title: "Quantumness and Dequantumness Power of Quantum Channels"
doi: 10.3390/e24081146
url: https://europepmc.org/article/PMC/PMC9407519
claim: "The quantumness of an ensemble {(p_i, rho_i)} is minus the weighted sum of tr[rho_i, rho_j]^2. The dequantumness power D of a channel is the largest decrease of quantumness over input ensembles, and D' restricts the inputs to ensembles of maximal quantumness; D_2 and D_2' are the two-ingredient versions. For amplitude damping the paper finds D_2 = D_2' and conjectures that this equality may fail for other channels."
strata_touched:
  - D5/S3/QuantumChannels/DequantumnessPowerStrictGap
license: citation-only
triage: anchor
---

# Song and Li, Quantumness and dequantumness power of quantum channels

H. Song and N. Li, Entropy 24(8), 1146 (2022). No arXiv version was found. Quotations are from the Europe PMC full-text XML of PMC9407519, with formulas transcribed from its MathML.

Section 2 measures the quantumness of an ensemble $\mathcal E=\{(p_i,\rho_i)\}$ by
$$Q(\mathcal E)=-\sum_{i,j}p_ip_j\,\mathrm{tr}[\rho_i,\rho_j]^2 .$$

Section 3 defines the dequantumness power of a channel $\Lambda$ as the largest decrease $D(\Lambda)=\max_{\mathcal E}\big(Q(\mathcal E)-Q(\Lambda(\mathcal E))\big)$, and a modified version over ensembles of maximal quantumness:

> When we only consider the initial ensembles with the maximal quantumness, we can obtain a modified version […] Here […] denotes the maximal amount of quantunness in a quantum ensemble for a given Hilbert space, which is dependent on the space dimension.

The conjecture, at the end of Section 3 after the amplitude-damping example:

> Though $D_2(\Lambda)=D_2'(\Lambda)$ in this case, we conjecture this equality may fail in certain cases. But we have not found the counterexample satisfying $D_2(\Lambda)>D_2'(\Lambda)$ yet.

## Verified locator

Source: https://doi.org/10.3390/e24081146
- DOI: https://doi.org/10.3390/e24081146 (Entropy 24(8), 1146; published online 18 August 2022; title, authors, journal, volume and issue from Crossref).
- URL: https://europepmc.org/article/PMC/PMC9407519. The Europe PMC REST full text `PMC9407519/fullTextXML` has 225,880 bytes and md5 `d8a14dae68ef8ac92304b0199d70137a`. Locations: Section 2 "Measure of Quantumness" (Eq. (1)); Section 3 "Quantumness and Dequantumness Power" (the definitions of $D$ and $D'$, the amplitude-damping example and the conjecture, at the end of the section).
