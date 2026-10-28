---
bibkey: ptaszynski2022skewness
authors: Krzysztof Ptaszyński
year: 2022
title: "Bounds on skewness and kurtosis of steady-state currents"
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
claim: "The paper derives bounds on the skewness and kurtosis of steady-state currents for several classes of systems; for unicyclic Markovian networks it infers numerically that the extremal values are attained when all clockwise rates are equal but one, and on that topology finds the minimum skewness -(8-8N+N^2)/(16(N-1)^2) of a unidirectional N-state cycle at a = 1/(N-1)."
strata_touched:
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum
license: citation-only
triage: anchor
---

# Ptaszyński, bounds on skewness and kurtosis of steady-state currents

K. Ptaszyński, arXiv:2204.08421v4 [cond-mat.mes-hall] (20 July 2022; v1 18 April 2022); Phys. Rev. E 106, 024119 (2022). Quotations are from the v4 TeX source, with the macros `\llangle`, `\rrangle` written as $\langle\!\langle$, $\rangle\!\rangle$ and cross-references omitted.

The skewness of a current:

> $\mathcal{S}=\frac{\langle\!\langle j^3 \rangle\!\rangle}{\langle\!\langle j^1 \rangle\!\rangle}$,

with the scaled cumulants $\langle\!\langle j^n\rangle\!\rangle$. For a unicyclic network the winding-number cumulants follow from the waiting-time cumulants (Appendix):

> $\langle\!\langle j^1 \rangle\!\rangle = \frac{1}{\kappa_1}$, $\langle\!\langle j^3 \rangle\!\rangle = 3\frac{\kappa_2^2}{\kappa_1^5}-\frac{\kappa_3}{\kappa_1^4}$, with $\kappa_1 = \sum_{i=1}^N k_{i+1,i}^{-1}$, $\kappa_2 = \sum_{i=1}^N k_{i+1,i}^{-2}$, $\kappa_3 = 2\sum_{i=1}^N k_{i+1,i}^{-3}$

for clockwise rates $k_{i+1,i}$ ($k_{N+1,N}=k_{1N}$). The unidirectional minimum and the conjectured extremal topology (Section III E 1):

> it was inferred that the bounds are always saturated for a specific type of network topology with $k_{21}=ak$ and $k_{ij}=k$ for $j>1$ … Assuming this type of network topology, the value of $a$ saturating the bounds has been then analytically determined: $\min(\mathcal{S})= -\frac{8-8N+N^2}{16(N-1)^2}$ for $a=\frac{1}{N-1}$, $\max(\mathcal{S})=1$ for $a \rightarrow 0$.

> it was numerically conjectured that the minimum and maximum values of $\mathcal{S}$, $\mathcal{K}$, $\mathcal{S}+\mathcal{K}$, $\mathcal{S}-\mathcal{K}$ and $\mathcal{S} \times \mathcal{K}$ are always obtained for a specific type of network topology, with all rates $k_{ij}$ equal to $k$ apart from one (here $k_{21}$) equal to $ak$.

## Verified locator

Source: https://arxiv.org/abs/2204.08421v4
- DOI: https://doi.org/10.1103/PhysRevE.106.024119 (Phys. Rev. E 106, 024119 (2022); author, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2204.08421v4 (the e-print is a gzipped tar archive; member `main.tex`, 1102 lines, md5 `5b72a7d5de1e5c34c76db21badb56492`):
  - the skewness, l. 53;
  - unidirectional networks and the minimum, Section III E 1, l. 416–431;
  - the winding-number cumulants and the waiting-time cumulants, Appendix, l. 768–790;
  - the numerically conjectured extremal topology, Appendix, l. 792.
- The author and the arXiv dates are from the arXiv metadata.
