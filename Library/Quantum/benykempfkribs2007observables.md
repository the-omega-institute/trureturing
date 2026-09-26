---
bibkey: benykempfkribs2007observables
authors: Cédric Bény and Achim Kempf and David W. Kribs
year: 2007
title: Quantum Error Correction of Observables
doi: 10.1103/PhysRevA.76.042303
claim: Correctable observable algebras can be characterized in the Heisenberg picture without requiring recovery of the whole physical state.
strata_touched:
  - D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel
license: citation-only
triage: anchor
---

# Correctable observables rather than an entire physical state

The paper develops operator-algebra quantum error correction in the Heisenberg
picture, including hybrid quantum-classical information. It supplies detailed
proofs and extensions of the authors' earlier PRL framework. This is an existing
literature anchor, not a novelty claim for the repository.

For the concrete orthogonal-syndrome construction, the repository's
`logicalRepresentation S A = sum_j S_j A S_j^*` is a faithful star-preserving
multiplicative representation when the syndrome family is nonempty. Its unit is
the support projection P, not necessarily the identity on the whole physical
space. The restriction to any one syndrome copy is a left inverse. These
finite-matrix statements specify exactly which logical observables survive.
They do not by themselves prove the general correctable-algebra classification,
smooth bundle trivialisation, a Chern-number theorem, or an infinite-dimensional
recovery theorem.

Primary sources:
- https://arxiv.org/abs/0705.1574
- https://doi.org/10.1103/PhysRevA.76.042303

Companion announcement: C. Bény, A. Kempf and D. W. Kribs, *Generalization of
Quantum Error Correction via the Heisenberg Picture*, Physical Review Letters
98, 100502 (7 March 2007), DOI 10.1103/PhysRevLett.98.100502,
arXiv:quant-ph/0608071. The detailed PRA paper was published 2 October 2007.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.76.042303 resolves to the Physical
  Review A article titled above.
- Preprint: https://arxiv.org/abs/0705.1574 .
- The cited scope is correctable observable algebras in the Heisenberg picture;
  the repository proves only its stated finite orthogonal-syndrome instance.
