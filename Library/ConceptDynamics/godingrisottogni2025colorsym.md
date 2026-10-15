---
bibkey: godingrisottogni2025colorsym
authors: Jean-Christophe Godin; Rémi Grisot; Olivier Togni
year: 2025
title: On List Coloring with Separation of the Complete Graph and Set System Intersections
doi: 10.5614/ejgta.2025.13.1.5
url: https://arxiv.org/abs/2209.03436
claim: "Section 3.1 conjectures that Algorithm ColorSym produces an (L, b)-coloring whenever K_n is (L, b)-colorable."
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/ColorSymOptimalityRefutation
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ConceptDynamics/godingrisottogni2025colorsym -->

# ColorSym optimality

## Verified locator

DOI: 10.5614/ejgta.2025.13.1.5

Source: https://arxiv.org/abs/2209.03436

The journal article appears in *Electronic Journal of Graph Theory and
Applications* 13(1), pp. 57–74. Section 3.1, p. 63, states:

> We conjecture that this algorithm is optimal (i.e., produces an (L, b)-coloring if K_n is (L, b)-colorable).

Section 1, pp. 57–58, defines an (L, b)-coloring as

> a coloring function φ on the vertices of G that assigns to each vertex v a subset of b elements from L(v) in such a way that φ(u) ∩ φ(v) = ∅ for any uv ∈ E(G)

Section 2.1, p. 59, defines proper intersections as the intersection of the
selected sets minus the union of the unselected sets. Section 3.1, p. 63,
assigns singleton proper intersections first and then processes larger supports
in increasing size, assigning each color to a least-loaded vertex and taking
the smallest index on ties. Its instructions include:

> If wi ≥ b for each i or i = n + 1, then Stop.

> let j ∈ S be the index for which w(j) is minimum (if more than one j with minimum w, then take the smallest index)

> Remove a color from Ip(S) and assign it to vj. Goto Step i until Ip(S) is empty.

The same conjecture occurs in Section 3.1 of arXiv:2209.03436v1. Corollary 15
of that version, renumbered Corollary 3.1 in the journal article, establishes
the symmetrical case. The repository's four-vertex assignment is not
symmetrical, and its refutation leaves that proved case intact.

The cited source supplies the definitions and conjecture. It does not supply
the repository's counterexample or its proof. Completeness of the prior-art
screen remains ASSUMED-UNVERIFIED.
