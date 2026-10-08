---
bibkey: george2024zerocommunication
authors: Ian George and Eric Chitambar
year: 2024
title: Reexamination of quantum state transformations with zero communication
doi: 10.1103/PhysRevA.109.062418
url: https://doi.org/10.1103/PhysRevA.109.062418
claim: Optimal bipartite pure-state conversion fidelity under local operations and shared randomness reduces to an auxiliary Schmidt-spectrum optimization; flat-target distillation uses descending block sums.
strata_touched: []
license: citation-only
triage: anchor
---

# Zero-communication pure-state conversion

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.109.062418

Primary accepted manuscript: https://link.aps.org/accepted/10.1103/PhysRevA.109.062418 . Theorem 4, printed pages 11–12, identifies the optimal pure-target fidelity under LO and LOSR. Theorem 8, printed pages 17–18, treats flat-target distillation using decreasing sums of source Schmidt amplitudes over target-size blocks. Proposition 11 concerns dilution in the opposite direction.

## Use and boundary

For target rank d and sorted source probabilities lambda, put b_j=d^(-1/2) sum_{a<d} sqrt(lambda_{dj+a}), with zero padding. Theorem 8's auxiliary-probability optimization has value sum_j b_j^2: Cauchy–Schwarz gives the bound and probabilities proportional to b_j^2 attain it. This single-state fidelity formula is literature-attested, including uniform-source noninteger rank ratios.

RT's coherent multisector extension uses these block amplitudes as one cross-sector Gram kernel, constructs a common finite cyclic-shift mixture, and proves an arbitrary-reference diamond optimum with orthogonal output leakage. Those channel quantifiers are not supplied by the cited state-fidelity theorem. Equality of LO and LOSR fidelity does not imply equality of their trace-distance optima. No global priority claim for the separate channel result is made here.
