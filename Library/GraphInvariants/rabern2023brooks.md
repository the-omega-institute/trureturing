---
bibkey: rabern2023brooks
authors: Landon Rabern
year: 2023
title: "Yet another proof of Brooks' theorem"
doi: 10.1016/j.disc.2022.113261
url: https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d
claim: "Brooks' maximum-degree coloring alternative, using clique and odd-cycle exceptions."
strata_touched:
  - D5/S3/Combinatorics/Graph/Brooks/ColoringExtension
  - D5/S3/Combinatorics/Graph/Brooks/CliqueExtension
  - D5/S3/Combinatorics/Graph/Brooks/Surgery
  - D5/S3/Combinatorics/Graph/Brooks/General
license: citation-only
triage: anchor
---

# Brooks' coloring alternative

## Verified locator

https://doi.org/10.1016/j.disc.2022.113261

https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d

The code supplier credits the mathematical argument to Landon Rabern,
Discrete Mathematics 346 (2023), article 113261. The paper's full text is
not the source of the code transplant. Brian Rabern's BrooksLean source,
with code authors Brian Rabern and Opus 5, gives the arbitrary-degree
maximum-clique or degree-two odd-cycle alternative. Its Apache-2.0
license is retained in docs/reports/brooks-suppliers/BrooksLean-LICENSE.txt.

The connected-graph consequence uses saturation of each clique or cycle
vertex's neighbor set. Connectedness then exhausts the graph, and a
finite bijection identifies the cycle with the native cycle graph.

The supplier units are pinned at that revision: BrooksLean/OddCycle.lean,
BrooksLean/VertexLemmas.lean, and BrooksLean/Brooks.lean. The retained proof
is organized as ColoringExtension (odd cycles, degree reduction and coloring
tools), CliqueExtension (almost-clique and Hall color extensions), Surgery
(Rabern's clique and odd-cycle steps), and General (Brooks and the connected
exception constructions). The existing Coloring owner supplies the
low-degree vertex-deletion extension.

The connected clique-completeness, cycle support/edge exhaustion and actual
cycle-isomorphism proofs are continuation additions, rather than claims of
the supplier's raw Brooks theorem. A three-cycle is complete; the separate
noncomplete odd-cycle alternative has length at least five. These results
do not prove the Hartnell–Rall–Wash Cartesian-product obstruction.

Retire each transplanted statement when this repository's own pinned Mathlib
contains an equivalent statement, redirecting its consumers to that owner.
