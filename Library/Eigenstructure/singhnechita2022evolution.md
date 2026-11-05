---
bibkey: singhnechita2022evolution
authors: Satvik Singh; Ion Nechita
year: 2022
title: "Diagonal unitary and orthogonal symmetries in quantum theory II: Evolution operators"
doi: 10.1088/1751-8121/ac7017
url: https://arxiv.org/abs/2112.11123v1
claim: "The paper studies bipartite unitary and orthogonal evolution operators with diagonal symmetries and their entangling power; for the real case it introduces the Hadamardness measure Tr[(CC*)^2] of a sign matrix C, shows it is at least d^3 with equality exactly for Hadamard matrices, tabulates its minimum for d = 3, 5, 6, and conjectures that for every odd d the minimum is d^3 + d(d-1)."
strata_touched:
  - D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation
license: citation-only
triage: anchor
---

# Singh and Nechita, diagonal unitary and orthogonal symmetries in quantum theory II

S. Singh and I. Nechita, arXiv:2112.11123v1 [quant-ph] (21 December 2021); J. Phys. A: Math. Theor. 55 (2022) 255302. Quotations are from the v1 TeX source, with the macros `\overbar`, `\iden` written as $\overline{\cdot}$, $I$ and cross-references omitted.

The Hadamardness measure of a sign matrix $C\in\mathcal M_d(\{\pm1\})$:

> $\mathfrak h(C) = \operatorname{Tr}[(CC^\dagger)^2] = \sum_{i,j=1}^d |\langle C_{i,\cdot}, C_{j, \cdot} \rangle|^2 = \sum_{i,j=1}^d \left|\sum_{k=1}^d C_{ik}\overline{C_{jk}} \right|^2$,

with the lemma

> For a sign matrix $C\in \mathcal M_d(\{\pm 1\})$, we have $\mathfrak h(C) \geq d^3$, with equality being attained if and only if $C$ is a Hadamard matrix ($CC^\dagger = dI_d$).

A table lists the minima $33$, $145$, $264$ for $d=3,5,6$ obtained by enumerating sign matrices. The conjecture:

> We note that for the odd values of $d$ considered above, $\min \mathfrak h(C) = d^3 + d(d-1)$, obtained for matrices $C$ with the property that all the scalar products between different works have absolute value $1$. We conjecture that this is the case for all odd integers $d$.

("works" is the source's wording for rows.)

## Verified locator

Source: https://arxiv.org/abs/2112.11123v1
- DOI: https://doi.org/10.1088/1751-8121/ac7017 (J. Phys. A 55, 255302 (2022); author list, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2112.11123v1 (the e-print is a gzipped tar archive; member `main.tex`, 1078 lines, md5 `d14ae7d4973cb1e432691fa8f590bb01`):
  - the Hadamardness measure, Eq. `eq:Hada_measure`, l. 780–783;
  - the lemma $\mathfrak h(C)\ge d^3$, l. 785–792;
  - the table of minima, l. 796–846;
  - the conjecture, l. 848.
- The author list and the arXiv date are from the arXiv metadata.
