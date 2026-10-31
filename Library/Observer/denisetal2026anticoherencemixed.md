---
bibkey: denisetal2026anticoherencemixed
authors: Jérôme Denis, Tara Lacaille, John Martin and Eduardo Serrano-Ensástiga
year: 2026
title: "Total, quantum, and classical measures of anticoherence for mixed spin states"
doi: 10.48550/arXiv.2605.29436
url: "https://arxiv.org/abs/2605.29436v1"
claim: "The paper axiomatizes total t-anticoherence measures for mixed spin-j states, including monotonicity (T4) under SU(2)-covariant channels, proves (T4) for the Hilbert–Schmidt distance-based measure, and leaves open whether (T4) holds for the trace-distance-based measure."
strata_touched:
  - D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation
license: citation-only
triage: anchor
---

# Denis, Lacaille, Martin and Serrano-Ensástiga, Total, quantum, and classical measures of anticoherence for mixed spin states

J. Denis, T. Lacaille, J. Martin and E. Serrano-Ensástiga, arXiv:2605.29436v1 (2026). Quotations are from the v1 TeX source.

A spin-$j$ state $\rho$ is identified with a symmetric state $\rho_S$ of $N=2j$ qubits, and $\rho_t=\operatorname{Tr}_{N-t}(\rho_S)$ is its $t$-qubit reduction, defined for every $t\in\{1,\dots,N\}$. A total $t$-anticoherence measure must satisfy, among other axioms,

> (T4) Monotonicity under $\mathrm{SU}(2)$-covariant noise: For every $\mathrm{SU}(2)$-covariant channel $\Phi:\mathcal D(\mathcal H_j)\to\mathcal D(\mathcal H_j)$, […] one has $\mathcal A^T_t(\Phi(\rho))\ge\mathcal A^T_t(\rho)$ for all $\rho\in\mathcal D(\mathcal H_j)$.

The distance-based candidates are $\mathcal A^{T,d}_t(\rho)=1-d(\rho_t,\mathbb 1_{t+1}/(t+1))/K_t$ with $K_t$ the largest possible distance. After proving (T4) for the Schatten-2 distance, the paper states:

> We also find numerical evidence that axiom (T4) remains valid for the trace-distance case $p=1$; a proof is left open.

## Verified locator

Source: https://arxiv.org/abs/2605.29436v1
- DOI: https://doi.org/10.48550/arXiv.2605.29436 (the arXiv-issued DataCite DOI; title, authors and year from DataCite; the abstract page lists v1 only).
- URL: https://arxiv.org/abs/2605.29436v1. The e-print member `arxiv.tex` has 1647 lines and md5 `cc8e7241680606ee66e21581554aa985`. Locations:
  - the symmetric-subspace identification and $\rho_t$, l. 150–161;
  - the range of $t$, footnote at l. 178;
  - axiom (T4), l. 180–200;
  - distance-based measures, l. 333–358;
  - Proposition 2 and the open trace-distance case, l. 359–363.
