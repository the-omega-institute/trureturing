---
bibkey: schnellketzmerickeckardt2018bose
authors: Schnell, Alexander; Ketzmerick, Roland; Eckardt, André
year: 2018
title: "On the number of Bose-selected modes in driven-dissipative ideal Bose gases"
doi: 10.1103/PhysRevE.97.032136
url: "https://arxiv.org/abs/1802.04088v2"
claim: "The paper characterizes the Bose-selected states of driven-dissipative ideal Bose gases by the condition mu = A eta on the rate-asymmetry matrix, shows that two ohmic baths with product coupling select at most three states (M_S <= 2 M_B - 1 for M_B baths), and expects the same bound for non-ohmic spectral densities |epsilon|^d sgn(epsilon)."
strata_touched:
  - D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation
  - D5/S3/StatisticalMechanics/BoseSelectionFixedBathConstruction
  - D5/S3/StatisticalMechanics/BoseSelectionFixedOrthogonalBaths
license: citation-only
triage: anchor
---

# Schnell, Ketzmerick and Eckardt, On the number of Bose-selected modes in driven-dissipative ideal Bose gases

A. Schnell, R. Ketzmerick and A. Eckardt, Phys. Rev. E 97, 032136 (2018), DOI 10.1103/PhysRevE.97.032136; arXiv:1802.04088v2. Quotations are from the arXiv v2 TeX source `main.tex`; macros are expanded.

The selected set $S$ of single-particle states is characterized by $\mu=A\eta$ with $\mu_i=0$, $\eta_i>0$ for $i\in S$ and $\mu_i<0$, $\eta_i=0$ for $i\notin S$ (l. 373–381), a condition that "has been shown to uniquely determine the set of the selected states" (l. 367). For two baths coupled through $|f\rangle\langle f|$ and $|g\rangle\langle g|$ with $J_{B_2}=-J_{B_1}=-J$, the rate-asymmetry matrix is $A_{ij}=\frac{2\pi}{\hbar}J(\varepsilon_j-\varepsilon_i)(f_if_j-g_ig_j)$ with $f_i=|\langle i|f\rangle|^2$, $g_i=|\langle i|g\rangle|^2$ (l. 1066–1083). For two ohmic baths "the number of Bose-selected states is restricted to a maximum of three" (l. 1145–1146), and $M_B$ baths give $M_S\le2M_B-1$ (l. 1170). The paper then states (l. 1173–1179):

> We expect that there is a generalization of the above arguement also to non-ohmic systems described by arbitrary spectral densities. We have checked functions of the form (remember that $J$ must be odd) $J(\varepsilon)\propto|\varepsilon|^d\,\mathrm{sgn}(\varepsilon)$ with some power $d$ (not necessarily integer) and similarly observe $M_S\le2M_B-1$.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevE.97.032136
- Source: https://arxiv.org/abs/1802.04088v2

## Ma–Zhang fixed orthogonal bath continuation

Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University
of Singapore; ChronoAI Pte Ltd, Singapore), 10 November 2026. This is a
continuation in the existing Schnell–Ketzmerick–Eckardt research family,
not a new counted paper or an independently established priority claim.
The URL locates the receiving issue, not a publication or acceptance record.

The complete three-page supplied PDF has SHA256
`846e57fdd424798b9f1e83d03e49bdc1e2c250f54111ce839f8982fc1d00b7c5`;
its TeX has SHA256
`0022ec412fa55d49a4f8a4381e72de348d765c063d61f2ed187eb8b84ca611d2`.
Source release 440890785 also supplies an exact finite checker. Its examples
in dimensions 6, 7, 8 and 20 do not prove the arbitrary-dimension theorem.

The model and strict selection condition are Schnell, Ketzmerick and
Eckardt, Physical Review E 97, 032136 (2018),
[arXiv:1802.04088v2](https://arxiv.org/abs/1802.04088v2), equations (11),
(49)–(55), Section V and Figure 7. The signed principal-Pfaffian method is
Knebel, Weber, Krüger and Frey, Nature Communications 6, 6977 (2015),
[arXiv:1504.07816v1](https://arxiv.org/abs/1504.07816v1), Methods equation (19).
The orthogonal witness and its finite-dimension extension belong to the
Ma–Zhang source, licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

The formal construction covers all finite M≥5 over the real
and complex fields, rank-four selected blocks, global normalized uniqueness,
the intrinsic spectral-rate bridge, nonempty open matrix sets at exponent
three and a matrix-dependent local exponent neighborhood. It does not
identify the actual GOE or GUE laws, prove their full support, or formalize
the separate common interval |d−3|≤1/128 from the supplied uniform certificate.
The written probability argument and that interval must not be reported as
current Lean conclusions. No dimension-uniform neighborhood size, uniform
probability lower bound, seven-mode result or other physical-model result
is inferred. The earlier BS1–BS8 source record remains in scope with its
original domains and unresolved obligations.
