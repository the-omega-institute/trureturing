---
bibkey: schmerltrotter1993critical
authors: James H. Schmerl and William T. Trotter
year: 1993
title: Critically indecomposable partially ordered sets, graphs, tournaments and other binary relational structures
doi: 10.1016/0012-365X(93)90516-V
url: https://trotter.math.gatech.edu/papers/83.pdf
claim: The classical odd-order critical tournament family T_r^(3) is a transitive chain together with one pivot oriented toward alternating chain vertices and away from the others.
strata_touched:
  - D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence
license: citation-only
triage: anchor
---

<!-- GID: D5/L/ConceptDynamics/schmerltrotter1993critical -->

# Critical binary relational structures

On page 198, Schmerl and Trotter define the tournament family denoted
`T_r^(3)`. Its vertices consist of a linearly ordered chain and one additional
vertex whose incident arcs alternate along that chain. After changing from
one-based to zero-based chain labels, the additional vertex points to the even
labels and receives arcs from the odd labels. The repository uses this
classical W family at odd orders at least seven and adds one sink to the
preceding odd-order W at even orders at least eight; both constructions have
the displayed alternating-pivot relation. The even-order extension is not
identified here as a classical critically indecomposable W tournament.

The paper studies critical indecomposability. No exact all-order
link-irregular tournament existence theorem was located in its inspected
statements; text extraction elsewhere in the PDF had imperfect OCR. In the
repository proof, after deleting a chain vertex, the surviving pivot is the
unique vertex whose further deletion leaves a transitive tournament: three
disjoint adjacent chain pairs ensure that deleting any other vertex leaves
an intact triangle. A chain-deleted-card isomorphism therefore fixes the
pivot and then the chain ranks, exposing opposite pivot-edge parity at the
smaller deleted rank. The pivot-deleted card itself is transitive, whereas
each chain-deleted card is not.

## Verified locator

- DOI: https://doi.org/10.1016/0012-365X(93)90516-V
- Author-hosted PDF: https://trotter.math.gatech.edu/papers/83.pdf
