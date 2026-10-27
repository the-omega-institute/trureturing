---
bibkey: bibakdelsantodakic2024coherence
authors: Fatemeh Bibak; Flavio Del Santo; Borivoje Dakić
year: 2024
title: "Quantum coherence in networks"
doi: 10.1103/PhysRevLett.133.230201
url: https://arxiv.org/abs/2407.11122v1
claim: "The paper defines a network figure of merit C_n distinguishing coherent n-party distributions from classical mixtures of two product distributions, computes the quantum value 1/2 - 2^{-n}, and from numerical optimization for n = 2, …, 10 conjectures that the classical maximum of C_n is 1/4 for all n."
strata_touched:
  - D5/S3/QuantumBounds/NetworkCoherenceClassicalBound
license: citation-only
triage: anchor
---

# Quantum coherence in networks

F. Bibak, F. Del Santo and B. Dakić, arXiv:2407.11122v1 [quant-ph]; Phys. Rev. Lett. 133 (2024). Quotations are from the v1 TeX source.

The classical model:

> $p_{\text{cl}}(a_1,a_2,a_3,\dots,a_n) = \gamma \,p_1(a_1) p_2(a_2) \dots p_n(a_n) + (1-\gamma) \,q_1(a_1) q_2(a_2) \dots q_n(a_n)$, where $\gamma$ is the probability of particles being distributed clockwise, and $p_j(a_i)$ ($q_j(a_i)$) is the probability that $j$th station outcomes $a_i$ given that the particles are sent in clockwise (counterclockwise) direction.

The figure of merit:

> $C_n = \frac{1}{2} \Bigg| \sum_{\vec{A}, \vec{A}^{\prime} \in \{0,1\}^n,\ \vec{A}^{\prime} \neq \vec{A},\ \bigoplus_{i=1}^{n} a_i^{(\prime)} = 0} p(\vec{A}) p(\vec{A}^{\prime}) - \sum_{\vec{B}, \vec{B}^{\prime} \in \{0,1\}^n,\ \vec{B}^{\prime} \neq \vec{B},\ \bigoplus_{i=1}^{n} b_i^{(\prime)} = 1} p(\vec{B}) p(\vec{B}^{\prime}) \Bigg|$

(the summation subscripts are written on one line here).

The quantum value:

> One can observe that the logical maximum of \( C_n \), achieved with quantum resources (Eq.~\eqref{psiinn}), is given by $C_n^Q = \binom{2^{n-1}}{2} \left( \frac{1}{2^{n-1}} \right)^2 = \frac{1}{2} - 2^{-n}.$

The conjecture:

> We obtained classical bound \( C_n^{\text{cl}} \) by substituting \( p_{\text{cl}} \) (Eq.~\eqref{pncl}) into the expression for \( C_n \) and performing extensive numerical optimization. For all tested values of \( n \in \{2, \ldots, 10\} \), we consistently obtained \(\text{max}(C_n^{\text{cl}}) = \frac{1}{4} \). Consequently, we conjecture that \(\text{max}(C_n^{\text{cl}}) = \frac{1}{4}\) for all \( n \).

## Verified locator

Source: https://arxiv.org/abs/2407.11122v1
- URL: https://arxiv.org/abs/2407.11122v1 (source `main.tex`, md5 `c47930e35162d18bc08d65fb1201100d`):
  - the classical model, l. 248–253;
  - the figure of merit, l. 259–268;
  - the quantum value, l. 272–276;
  - the conjecture, l. 277–278.
- DOI: 10.1103/PhysRevLett.133.230201 (https://doi.org/10.1103/PhysRevLett.133.230201; Crossref lists Physical Review Letters, volume 133, issued 2 December 2024).
