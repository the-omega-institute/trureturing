---
bibkey: streifleib2020forbidden
authors: Michael Streif; Martin Leib
year: 2020
title: "Forbidden subspaces for level-1 quantum approximate optimization algorithm and instantaneous quantum polynomial circuits"
doi: 10.1103/PhysRevA.102.042416
url: https://arxiv.org/abs/2007.13563v1
claim: "The paper characterizes diagonal problem Hamiltonians for which the level-1 QAOA state has unit overlap with a target subspace spanned by computational basis states. It treats one and two target states, and, assuming that the only mixing angles solving its necessary condition are odd multiples of pi/4, states that level-1 QAOA cannot reach a genuine superposition of more than 2 and fewer than 2^n target states; it conjectures that those angles are the only solutions."
strata_touched:
  - D5/S3/Quantum/Dynamics/LevelOneQAOAGenuineSuperposition
license: citation-only
triage: anchor
---

# Streif and Leib, Forbidden subspaces for level-1 QAOA and IQP circuits

M. Streif and M. Leib, arXiv:2007.13563v1 [quant-ph]; Physical Review A 102(4) (2020), 042416. Quotations are from the v1 TeX source.

The level-1 QAOA state is $e^{-i\beta H_X}e^{-i\gamma H_P}\lvert+\rangle$ with $H_X=\sum_i\sigma_x^{(i)}$, $\lvert+\rangle$ the uniform superposition of all computational basis states, and $H_P=\mathrm{diag}(E_l)$ a Hamiltonian diagonal in the computational basis. Deterministic QAOA asks for unit overlap with the span of $T$ target states that "can be ground states of a generic $N$-qubit Hamiltonian that is diagonal in the computational basis". A necessary condition is

> $$|z_l| = \frac{1}{\sqrt{2^n}} \qquad \forall \hspace{1mm} l \in \{0,1\}^n\,.$$

Section "More than two target states":

> Based on the assumption that the only solution can be found for $\beta = \frac{1}{4} \pi, \frac{3}{4} \pi, \frac{5}{4} \pi, \frac{7}{4} \pi$ we show in the following that level-1 QAOA can not map to a genuine superposition of more than $2$ but less than $2^n$ target states. We consider a genuine superposition of target states a superposition where no amplitude vanishes.

> Based on this observation as well as the calculation for the 2 target state case and numerical investigations we conducted we conjecture that the only possible solutions are $\beta = \frac{1}{4} \pi, \frac{3}{4} \pi, \frac{5}{4} \pi, \frac{7}{4} \pi$.

The abstract states the consequence as a result:

> We further show that there are no genuine solutions for target subspaces of dimension higher than $2$ and smaller than $2^n$.

## Verified locator

Source: https://arxiv.org/abs/2007.13563v1
- DOI: https://doi.org/10.1103/PhysRevA.102.042416 (Physical Review A 102(4), 042416; published 28 October 2020; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2007.13563v1. The e-print is a gzipped tar archive; its member `main.tex` has 419 lines and md5 `7638acf2f9652249b7c55d9b71550c4c`. Locations:
  - abstract, l. 71;
  - Section `sec:qaoa`, l. 96; the QAOA state, l. 100–108;
  - Section `sec:spectralprops`, l. 118; the target states, l. 124; Eq. (`eq:condition2`), l. 145–147;
  - Section `sec:manytargets`, l. 335; the statement and the conjecture, l. 336–341.
- The arXiv record lists only v1 (24 July 2020), with the journal reference "Phys. Rev. A 102, 042416 (2020)" (arXiv API metadata).
