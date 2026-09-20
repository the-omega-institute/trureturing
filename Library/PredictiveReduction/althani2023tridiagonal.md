---
bibkey: althani2023tridiagonal
authors: Hessa Al-Thani; Jon Lee
year: 2023
title: Tridiagonal maximum-entropy sampling and tridiagonal masks
doi: 10.1016/j.dam.2023.04.020
url: https://arxiv.org/abs/2112.12814v2
claim: Special support structures permit dynamic programming for maximum-entropy sampling; the repository's modal minimum-KL objectives and approximation guarantees require separate proofs.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Graph structure and exact versus approximate optimization

Discrete Applied Mathematics 337 (2023), 120–138, with the DOI above. The arXiv v2 parsed text, Section 2, and title metadata were read. Screenshot requests failed; no visual page inspection is attested. The paper proves polynomial algorithms for tridiagonal maximum-entropy sampling and extends the support-graph approach to specified bounded-leg spiders. Its objective is a maximum principal log-determinant.

Unified theory Section 14 uses graph structure for a different objective: minimum posterior-recovery KL over discarded complete oscillator modes. Its support graph is the off-block statistical precision graph, not the physical interaction graph. The tree recurrence for the second-order objective is standard dynamic programming. The additional proof controls its difference from the actual KL optimum using bipartite spectral symmetry and a one-sided fourth-order remainder.

The rounded-Schur continuation instead discretizes boundary precision messages and proves an arbitrary additive-error budget on block forests. The source's exact tridiagonal result cannot be broadened into a general exact forest determinant solver. Its Section 2 also notes that connected-subset enumeration can be exponential even for trees. The continuation therefore explicitly bounds its finite message state count instead of enumerating all connected components.

This note does not establish originality of the repository combinations or attribute their minimum-KL guarantees to the source. The cited existing Lean declaration concerns observable closure, not the new optimization results.
