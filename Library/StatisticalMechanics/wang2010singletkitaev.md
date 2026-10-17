---
bibkey: wang2010singletkitaev
authors: Fa Wang
year: 2010
title: "Realization of the Exactly Solvable Kitaev Honeycomb Lattice Model in a Spin Rotation Invariant System"
doi: 10.1103/PhysRevB.81.184416
url: https://arxiv.org/abs/1001.0266v2
claim: "Four-spin singlet pseudospins, their physical exchange/chirality representation, and exact or perturbative encoded Kitaev constructions."
strata_touched: []
license: citation-only
triage: anchor
---

## Verified source scope

Physical Review B 81, 184416 (2010), arXiv v2 dated 4 May 2010. The paper's Section II and Table I identify the two-dimensional singlet multiplicity of four spin-1/2 moments and give exchange and scalar-chirality representatives of its Pauli operators. Its exact encoded Hamiltonian allows interactions involving up to six or eight physical spins. The singlet pseudospin carrier and its use in many-body modeling predate the present HS4 continuation.

Section IV.B and Appendix B construct perturbative inter-cluster terms. A physical vector operator sends a singlet into a triplet, making the first-order projected inter-cluster exchange vanish and giving the second-order denominator 2 J_cluster. The paper's chirality-axis coupling uses microscopic three-spin scalar-chirality perturbations; it is not restricted to real bilinear inter-cluster Heisenberg terms.

The parsed text of these sections was inspected. PDF screenshot retrieval failed, so no claim is based on an unseen figure or screenshot. The formulas used for comparison are present in the parsed text. The paper contains an established method and important prior constructions; absence of a particular formula here is not an exhaustive priority search.

## Precise correspondence to the new theory

[HS4 many-body exchange](../../docs/develop/theory/HIGUCHI_SUDBERY_MANY_BODY_EXCHANGE.md) uses the same spin-zero carrier with a specified real basis, single-cell gap Delta=J_cluster, and a real 4-by-4 matrix of exclusively bilinear cross-cell couplings. The chapter derives its arbitrary-matrix cubic YY coefficient, finite resolvent remainder, matched-link eight-spin ground-state bounds and matched-label graph-triangle correction directly. These formulas are not attributed to Wang, and their historical priority is not asserted.

The second-order projection and pseudospin interpretation are reused established methods. In particular a new coefficient-level absence of YY at second order is scoped to the real bilinear perturbation class, and does not contradict the paper's wider microscopic interaction menu. An exact encoded Kitaev model using high-body terms and a truncated low-energy model using bilinear terms also have different error contracts.

## Related primary sources

H. Tsunetsugu, *Antiferromagnetic Quantum Spins on the Pyrochlore Lattice*, [arXiv:cond-mat/0103231](https://arxiv.org/abs/cond-mat/0103231), gives earlier chiral tetrahedral doublets and geometry-dependent effective interactions. S. Bravyi, D. P. DiVincenzo and D. Loss, *Schrieffer-Wolff transformation for quantum many-body systems*, [arXiv:1105.0675](https://arxiv.org/abs/1105.0675), gives the general effective-Hamiltonian and linked-cluster framework. The present finite Schur-complement estimate is explicitly derived in the chapter and is not represented as a size-uniform theorem imported from that source.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevB.81.184416
- Source: https://arxiv.org/abs/1001.0266v2
