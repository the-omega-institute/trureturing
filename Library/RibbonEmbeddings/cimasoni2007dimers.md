---
bibkey: cimasoni2007dimers
authors: David Cimasoni, Nicolai Reshetikhin
year: 2007
title: Dimers on surface graphs and spin structures. I
doi: 10.1007/s00220-007-0302-7
url: https://arxiv.org/html/math-ph/0608070v2
claim: Theorem 3.1 characterizes existence of Kasteleyn orientations on closed oriented surface graphs by even vertex cardinality.
strata_touched:
  - D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary
  - D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces
  - D5/S3/Combinatorics/PerfectMatchings/AlternatingCyclePfaffian
license: citation-only
triage: anchor
---

# Dimers on surface graphs

Theorem 3.1 states that a surface graph admits a Kasteleyn orientation
exactly when its number of vertices is even. The proof starts with an
arbitrary edge orientation, records the face defects as a binary
two-cochain, and uses the even Euler characteristic of a closed oriented
surface. Flipping the edges of a suitable one-cochain removes the defects.
Facial traversals count edge occurrences, so a bridge contributes both darts.

The finite rotation model in `RotationFaces` uses actual `SimpleGraph.Dart`
and all integer-power face orbits. Its face-boundary exactness and
off-cycle separation are combinatorial ingredients for this literature
route. Their statements do not assert geometric realization of a rotation
system, a topological disk theorem, a Pfaffian identity, or complexity bounds.
The signed regional Euler identities and directed-boundary correspondence
feed the face-odd orientation and nice-even-cycle endpoint on that same
actual graph. The complement matching restricts through the proved
no-cross-edge result, rather than supplying interior parity as a premise.

## Dimer coefficients and composition cycles

Cimasoni and Reshetikhin, *Dimers on surface graphs and spin structures. I*,
Section 5.1, writes a dimer coefficient as the sign of a vertex-pair listing
multiplied by the directed-edge signs. The proof of its Pfaffian expansion
compares two configurations along their composition cycles. For one even
alternating cycle, the coefficient ratio is minus the product of the
oriented edge signs around that cycle. Odd opposition therefore preserves
the coefficient under the flip.

The conditional simple-graph identity in the repository uses this algebraic
relation. Its public orientation hypothesis concerns actual simple even
cycles whose induced vertex-deleted complement has an actual perfect
matching. Uniformity follows by removing cycles from the actual symmetric
difference. The denominator-free standard Pfaffian sums over all pairings;
unsupported pairings contribute zero, and supported pairings correspond
to actual perfect-matching subgraphs. The resulting integer unit is
independent of weights and coefficient ring. Over the reals, nonnegative
weights give the absolute-value partition-function formula.

The surface-embedding, spin-structure and homology assertions of the paper
are separate from this conditional algebraic statement. The repository
statement neither supplies planar orientation existence nor asserts a
geometric realization or complexity bound. No Lean source from this paper
is adopted.


## Verified locator

- Primary version: https://arxiv.org/abs/math-ph/0608070v2.
- Inspected primary HTML: https://arxiv.org/html/math-ph/0608070v2,
  Section 3.1, Theorem 3.1 and its proof.
- Section 1.1 defines composition cycles. Section 5.1, “The Kasteleyn matrix
  and its Pfaffian,” gives the matching permutation coefficient, weighted
  Pfaffian expansion and composition-cycle sign comparison.
- Journal locator: https://doi.org/10.1007/s00220-007-0302-7.

The theorem and proof above are present in the primary HTML. The surface
embedding assumptions in that theorem are stronger than the bare finite
rotation data; the note supplies literature context rather than a formal
geometric-to-combinatorial equivalence.
