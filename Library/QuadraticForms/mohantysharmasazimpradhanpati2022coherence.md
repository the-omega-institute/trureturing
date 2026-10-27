---
bibkey: mohantysharmasazimpradhanpati2022coherence
authors: Sanuja D. Mohanty; Gautam Sharma; Sk Sazim; Biswajit Pradhan; Arun K. Pati
year: 2022
title: "Creation of quantum coherence with general measurement processes"
doi: 10.1007/s11128-021-03394-5
url: https://arxiv.org/abs/2004.10875v2
claim: "The paper studies how nonselective measurements, acting by the Lüders rule with the square roots of POVM effects, create l1-norm coherence. For one-parameter qubit POVMs it computes the maximum output coherence (C+|r|)/2 and characterizes the states without coherence gain and those with maximal gain. For general two-outcome POVMs it obtains no closed form, leaves open which states admit no gain and which attain the maximal gain, and lists analytical results for two-outcome and n-outcome POVMs as future work."
strata_touched:
  - D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum
license: citation-only
triage: anchor
---

# Mohanty, Sharma, Sazim, Pradhan and Pati, creation of coherence by measurements

S. D. Mohanty, G. Sharma, Sk Sazim, B. Pradhan and A. K. Pati, arXiv:2004.10875v2 [quant-ph]; Quantum Information Processing 21, 48 (2022). Quotations are from the v2 TeX source, with figure references replaced by bracketed descriptions.

Measurements (Section 2): a POVM $\{E_i\}$, $E_i\ge0$, $\sum_iE_i=\mathbb I$, changes a state to

> $\rho^M=\sum_i\sqrt{E_i}\rho\sqrt{E_i}$

in the non-selective case, and the coherence is the $l_1$ norm $C_{l_1}(\rho)=\sum_{i\neq j}|\rho_{i,j}|$.

One-parameter POVMs (Section 3.1), for a qubit with Bloch vector $\vec r$:

> $\max_{\alpha,\lambda}C_{l_1}(\rho')=\frac{1}{2}\big(C_{l_1}(\rho)+\sqrt{C_{l_1}(\rho)^2+r_3^2}\big)$

General two-outcome POVMs $E_\pm=a_\pm\mathbb I\pm\vec a\cdot\vec\sigma$ (Section 3.2):

> We couldn't get the expression for $\max_{\{\vec{a},a_{\pm}\}}C_{l_1}(\rho'_{\pm})$ analytically [...] However in this case, we don't know yet for which states there can not be any coherence gain and for which states the coherence gain will be maximum.

Conclusion:

> As a future line of work, it would be interesting to obtain the analytical results for two outcome and n-outcome POVMs.

## Verified locator

Source: https://arxiv.org/abs/2004.10875v2
- DOI: https://doi.org/10.1007/s11128-021-03394-5 (Quantum Information Processing 21, 48 (2022); author list, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2004.10875v2 (the e-print is a gzipped tar archive; member `coh-measure.tex`, 1020 lines, md5 `4a3d0408f3156bdc86a47a97160298ce`):
  - the $l_1$ coherence, l. 109;
  - non-selective measurements, l. 127–130;
  - one-parameter POVMs and their maximum, l. 184–245 (the maximum at l. 230–231);
  - general two-outcome POVMs and the question, l. 246–298;
  - the conclusion, l. 505.
- The arXiv version dates are from the arXiv metadata.
