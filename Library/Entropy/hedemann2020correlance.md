---
bibkey: hedemann2020correlance
authors: Samuel R. Hedemann
year: 2020
title: "Correlance and discordance: computable measures of nonlocal correlation"
doi: 10.1007/s11128-020-02676-8
url: https://arxiv.org/abs/2001.03453v2
claim: "The paper defines the correlance of an N-mode state as the normalized squared Hilbert-Schmidt distance tr[(rho - varsigma)^2] between the state and the tensor product of its single-mode reductions, and related measures of nonlocal correlation. For diagonal input it normalizes by the maximum over all diagonal states and asserts that the equal mixture of the first and last basis projectors attains it in all systems, giving 1/2 - 1/2^N; the proof in the appendix is a sketch, and the paper says a rigorous proof is still lacking."
strata_touched:
  - D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation
license: citation-only
triage: anchor
---

# Hedemann, Correlance and discordance: computable measures of nonlocal correlation

S. R. Hedemann, arXiv:2001.03453v2 [quant-ph]; Quantum Information Processing 19(7) (2020), 189. Quotations are from the v2 TeX source, with the source's macros `\Correlance` ($\mathcal X$) and `\redx` (the single-mode reduction $\rho^{(m)}$) expanded.

Equations (10)–(11) define the raw correlance and the reduction product:

> $$\widetilde{\mathcal X}(\rho ) \equiv \mathrm{tr}[(\rho - \varsigma )^2 ],\qquad \varsigma \equiv \varsigma (\rho ) \equiv \bigotimes_{m = 1}^N \rho^{(m)} = \rho^{(1)} \otimes \cdots \otimes \rho^{(N)}.$$

Section II.C, "Correlance Adapted for Diagonal-Only Input", normalizes over the set of all diagonal states (Eq. (16)) and states:

> Instead, one simple example that maximizes $\mathcal X_D$ in all systems is
> $$\rho _{D_{\max } } = \frac{1}{2}(|1\rangle \langle 1| + |n\rangle \langle n|),$$
> yielding the normalization factor, valid for all systems,
> $$\mathcal{N}_{\mathcal X_D }=\widetilde{\mathcal X}(\rho _{D_{\text{max}}} )=\frac{1}{2}-\frac{1}{2^{N}}.$$

Appendix L gives a sketched proof; its Step 9 ends:

> However, a rigorous proof of this is still lacking.

The Conclusion adds:

> It would also be nice to have a more explicit proof of the normalization of diagonal correlance $\mathcal X_D$ rather than the sketch given in App. L, even though the numerical tests seem to vindicate it to excellent precision.

## Verified locator

Source: https://arxiv.org/abs/2001.03453v2
- DOI: https://doi.org/10.1007/s11128-020-02676-8 (Quantum Information Processing 19(7), 189; published online 20 May 2020; title, author, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2001.03453v2. The e-print is a gzipped tar archive; its member `CorrelanceAndDiscordance.tex` has 3721 lines and md5 `cd90edc790387e2e7754e6667f66a1ac`. Locations:
  - Section I.B, Eqs. (10)–(11), l. 302–312;
  - Section II.C, Eqs. (15)–(18), l. 440–466; Figure 4 caption, l. 476;
  - Conclusion, l. 1420;
  - Appendix L, Step 1, l. 2347; Step 9, l. 2385.
- The arXiv record lists v1 (9 January 2020) and v2 (30 May 2020), with the comment "v2: fixed small typos involving references; main results unchanged" and the journal reference "Quant. Inf. Process. 19, 189 (2020)" (arXiv API metadata).
