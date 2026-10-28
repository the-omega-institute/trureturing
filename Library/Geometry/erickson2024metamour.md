---
bibkey: erickson2024metamour
authors: William Q. Erickson, Daniel Herden, Jonathan Meddaugh, Mark R. Sepanski, Mitchell Minyard, Kyle Rosengartner
year: 2024
title: "Limits and Periodicity of Metamour 2-Distance Graphs"
doi: null
url: https://arxiv.org/abs/2409.02306v1
claim: "Theorem 4.1 characterizes fixed points of the metamour operator as edgeless graphs; the proof of Theorem 6.5 explicitly states that K_1 has metamour period one."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/DemoStrongPeriodBoundRefutation
license: citation-only
triage: anchor
---

# Known fixed points of the exact-distance-two operator

## Verified locator

The fixed source is [arXiv:2409.02306v1](https://arxiv.org/abs/2409.02306v1),
[original PDF](https://arxiv.org/pdf/2409.02306v1) and
[original HTML](https://arxiv.org/html/2409.02306v1).

The complete thirty-four-page original PDF and relevant HTML were inspected in
the source qualification. Definition 2.1 gives the metamour graph by adjacency
at exact shortest distance two. Theorem 4.1 states that a graph is a fixed point
exactly when it is edgeless. The proof of Theorem 6.5 explicitly notes that K_1
has metamour period one while excluding it from the period-two case.

These are prior literature facts. In particular the connected singleton and its
period one are not new. They support the elementary instance used against the
later conjecture in [demo2026periodicity](demo2026periodicity.md); this source
does not state a refutation of that later bound. The Lean proof uses the actual
distance and identity-isomorphism facts directly, without assuming this paper's
theorems or adding a separately packaged fixed-point theorem.
