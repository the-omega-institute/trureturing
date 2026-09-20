---
bibkey: goyal2019timelimited
authors: Pawan Goyal; Martin Redmann
year: 2019
title: Time-limited H2-optimal model order reduction
doi: 10.1016/j.amc.2019.02.065
url: https://arxiv.org/abs/1712.00301
claim: Finite-horizon input-output approximation, cross Gramians, and first-order H2 optimality conditions predate the repository's constrained posterior-rollout objective.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Finite-horizon model reduction

## Source and locator

The publisher record gives Applied Mathematics and Computation 355, 184–197 (2019), with the DOI above. The arXiv manuscript is titled *Towards Time-Limited H2-Optimal Model Order Reduction*, arXiv:1712.00301v1. These title variants are not separate contributions.

The parsed manuscript was checked at Section 2, equation (5), Lemma 2.1, and Section 3's optimality conditions. The PDF page containing equation (5) and Lemma 2.1 was also visually inspected. The manuscript treats a finite time interval and relates an input-output error objective to finite-time matrix integrals. Its iterative construction aims at the stated first-order conditions.

## Dependency boundary

Section 14 of `docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md` uses this as prior art for finite-horizon reduction. Its own optimization fixes posterior initialization, an orthogonal canonical encoder/decoder, and a reference generator class. A global spectral minimum in that restricted class is not a global solution of the source's unrestricted reduced-system problem.

No source algorithm or numerical benchmark was run. This note supplies attribution and scope, not an independent review of the paper or a Lean proof. The Scribe acknowledgement references an existing commutator-closure declaration only as the research interface.
