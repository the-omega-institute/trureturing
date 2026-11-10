---
bibkey: ptaszynski2022skewness
authors: Krzysztof Ptaszyński
year: 2022
title: "Bounds on skewness and kurtosis of steady-state currents"
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
claim: "The paper derives bounds on the skewness and kurtosis of steady-state currents for several classes of systems; for unicyclic Markovian networks it infers numerically that the extremal values are attained when all clockwise rates are equal but one, and on that topology finds the minimum skewness -(8-8N+N^2)/(16(N-1)^2) of a unidirectional N-state cycle at a = 1/(N-1); in the limit N -> infinity it gives the minimum kurtosis -(1+sqrt(5))/10 for a = A/N, A = (3-sqrt(5))/2, and the minimum of skewness plus kurtosis -8/27 for A = 1/2; it lists the product of skewness and kurtosis in [-0.054, 1] (eq. produni), the lower value approximate."
strata_touched:
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum
  - D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound
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

The kurtosis is $\mathcal{K}=\langle\!\langle j^4\rangle\!\rangle/\langle\!\langle j^2\rangle\!\rangle$ (l. 54). In the same section the remaining unidirectional bounds are obtained asymptotically:

> The other bounds have been derived in the assymptotic limit $N \rightarrow \infty$ in which the saturating value of $a$ scales as $a=A/N$. They read as $\min(\mathcal{K})= -\frac{1+\sqrt{5}}{10}$ for $A=\frac{3-\sqrt{5}}{2}$, $\max(\mathcal{K})=1$ for $A \rightarrow 0$, …

and, for the sum (l. 434–437):

> $\min(\mathcal{S}+ \mathcal{K})= -\frac{8}{27}$ for $A=\frac{1}{2}$, $\max(\mathcal{S}+\mathcal{K})=2$ for $A \rightarrow 0$

> it was numerically conjectured that the minimum and maximum values of $\mathcal{S}$, $\mathcal{K}$, $\mathcal{S}+\mathcal{K}$, $\mathcal{S}-\mathcal{K}$ and $\mathcal{S} \times \mathcal{K}$ are always obtained for a specific type of network topology, with all rates $k_{ij}$ equal to $k$ apart from one (here $k_{21}$) equal to $ak$.

## Verified locator

Source: https://arxiv.org/abs/2204.08421v4
- DOI: https://doi.org/10.1103/PhysRevE.106.024119 (Phys. Rev. E 106, 024119 (2022); author, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2204.08421v4 (the e-print is a gzipped tar archive; member `main.tex`, 1102 lines, md5 `5b72a7d5de1e5c34c76db21badb56492`):
  - the skewness, l. 53;
  - unidirectional networks, the skewness minimum and the asymptotic kurtosis minimum, Section III E 1, l. 407–432;
  - the asymptotic minimum of $\mathcal S+\mathcal K$, l. 434–437;
  - the winding-number cumulants and the waiting-time cumulants, Appendix, l. 768–790;
  - the numerically conjectured extremal topology, Appendix, l. 792.
- The author and the arXiv dates are from the arXiv metadata.

## Exact skewness-minus-kurtosis upper endpoint and source sign

The primary v4 source `main.tex`, SHA-256
`0d8f9bf311a07990b64d4746e9ec4fb1e164deec23b270503642b94766baf84e`,
line 432, states

> $\max(\mathcal S-\mathcal K)=3(107+51\sqrt{17})/2048$
> for $A=(5-\sqrt{17})/4$.

Figure 6 also concerns $\mathcal S-\mathcal K$. In contrast, the summary
at line 133 prints $\mathcal K-\mathcal S\in[-0.15,0.465]$.
These signs conflict. The difference endpoint formalization follows the
detailed display and figure; it does not silently read the summary as the
same formula. Line 424 uses $a=A/N$ in the infinite-size limit, and line 792
labels the general extremal-topology assertion numerical/conjectural. The
source's analytic evaluation on that topology is credited input; the
universal inference over arbitrary positive rate vectors requires proof.

The explicit finite realization with inverse rates $u$ and $N-1$ copies of
$(1-u)/(N-1)$, where $u=(9+\sqrt{17})/16$, has relative exceptional rate
$A/(N-1)$, not $A/N$, with $A=(1-u)/u=(5-\sqrt{17})/4$.
The ratio of the two relative rates is $N/(N-1)$ and tends to one.
Both finite families have positive rates; equality of their asymptotic
scaling does not identify their finite members.

The formal domain retains arbitrary positive real coordinates and repeated
rates. At $N=2$ its current interpretation uses two oriented phase stages
and a marked winding crossing. The formal expressions do not construct the
process, prove renewal asymptotics, or assert a physical $N=1$ case.
The independently inspected literature scopes found no exact supplier;
this is not a worldwide priority claim. The journal body and some
citation-list memberships remain unverified.

## Exact skewness-minus-kurtosis lower endpoint

The same primary v4 source and hash, `main.tex` line 431, state

> $\min(\mathcal S-\mathcal K)=3(107-51\sqrt{17})/2048$
> for $A=(5+\sqrt{17})/4$.

The detailed display and Figure 6 determine the sign used here; the
conflicting summary at line 133 remains as described above. The asserted
lower endpoint concerns the same scaled current cumulant ratios and the
same numerical extremal-topology conjecture. Its universal positive-rate
inequality and greatest-lower-bound interpretation do not assume that
conjectured topology.

For the explicit finite approximation with inverse rates $\alpha$ and
$N-1$ copies of $(1-\alpha)/(N-1)$, take
$\alpha=(9-\sqrt{17})/16$. Its relative exceptional rate is
$A/(N-1)$ with $A=(1-\alpha)/\alpha=(5+\sqrt{17})/4$.
This is a directly evaluated positive finite family; it is not identified
with the source's finite $A/N$ family. The domain and physical-interpretation
limits above also apply to this lower endpoint.
