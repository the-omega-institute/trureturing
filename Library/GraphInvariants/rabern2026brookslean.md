---
bibkey: rabern2026brookslean
authors: Brian Rabern
year: 2026
title: "BrooksLean: low-degree vertex coloring extension"
doi: null
url: https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d
claim: "An n-coloring after deleting a vertex extends to the whole graph when that vertex has fewer than n neighbors."
strata_touched:
  - D5/S3/Combinatorics/Graph/Brooks/Coloring
  - D5/S3/Combinatorics/Graph/Brooks/HereditaryColoring
license: Apache-2.0
triage: anchor
---

# Low-degree deletion and coloring extension: Lean source

The reused declaration is
`SimpleGraph.Colorable.of_induce_compl_singleton`:
if `(G.induce {v}ᶜ).Colorable n` and `G.degree v < n`, then `G.Colorable n`.
Its only finiteness assumption is `[Fintype (G.neighborSet v)]`.
The proof chooses a color absent from the neighbors and extends the deleted
vertex coloring.

## Verified locator

https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d

- Source repository: https://github.com/brianrabern/BrooksLean.
- Immutable revision: `1d990050d881327fc79dd51e82ba4449b4e2467d`.
- Exact declaration and proof: `BrooksLean/VertexLemmas.lean`, lines 19–56.
- Revision author: `brianrabern`; the repository identifies the project as
  an LLM-assisted Lean formalization of Rabern's inductive Brooks proof.
- Source pins: Lean `v4.33.0-rc1`, Mathlib
  `cb48454af87fbe318fc368e6eb02c9156e1936c1`.
- The source file imports only
  `Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex`.
- Full Apache-2.0 license:
  `docs/reports/brooks-suppliers/BrooksLean-LICENSE.txt`.
  The pinned repository has no NOTICE file and no per-file copyright header
  for `VertexLemmas.lean`.

## Reused scope and boundary

Only the low-degree deletion extension declaration is transplanted, with its
proof unchanged. The source's other greedy lemmas, odd-cycle development,
and full Brooks theorem are not part of this supplier dependency.
The retained declaration has an actual consumer in the hereditary sparsity
coloring proof. It is an existing result being reused, not a new mathematical
contribution.

The transplant is retired when this repository's pinned Mathlib contains an
equivalent declaration, replacing consumers by direct applications.
The source theorem supplies a single coloring-extension step; it does not
assert that an arbitrary graph of average degree at most three is
three-colorable or construct a covering-system repair.

The repository's published proof reference is Landon Rabern,
*Yet another proof of Brooks' theorem*, Discrete Mathematics 346 (2023),
113261, DOI https://doi.org/10.1016/j.disc.2022.113261.
For the standard deletion argument, Daniel W. Cranston and Landon Rabern,
*Brooks' theorem and beyond*, https://arxiv.org/abs/1403.0479v1, page 2,
explicitly explains that a vertex of a minimal counterexample must see every
color in a coloring of its deletion. The implementation author Brian Rabern
and cited paper author Landon Rabern are recorded separately.
