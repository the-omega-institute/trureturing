# Actual corner point periods

## Abstract

Minimal point returns enumerate the four actual ordered-corner components.

**Definition 1.1 (Ordered first endpoints).**

$$\forall c \in Fin\left(4\right),\; \forall s \in Fin\left(3\right),\; corner\left(c, s\right) = entry\left(((0, 2, 1), (1, 3, 2), (2, 0, 3), (0, 3, 1)), c, s\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.corner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rows L0, L1, H2, H0 have first-endpoint vectors (0,2,1), (1,3,2), (2,0,3), (0,3,1).

**Definition 1.2 (Ordered second endpoints).**

$$\forall c \in Fin\left(4\right),\; \forall s \in Fin\left(3\right),\; tip\left(c, s\right) = entry\left(((1, 3, 2), (0, 2, 1), (0, 3, 1), (2, 0, 3)), c, s\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.tip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The corresponding vectors are (1,3,2), (0,2,1), (0,3,1), (2,0,3). The pair (3,0) remains ordered. The twelve positions cover each j different from k exactly once; raw diagonal darts are excluded.

**Definition 1.3 (Forward face choices).**

$$\forall c \in Fin\left(4\right),\; \forall s \in Fin\left(3\right),\; outgoing\left(c, s\right) = entry\left(((2, 0, 0), (2, 0, 0), (1, 1, 0), (1, 1, 0)), c, s\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.outgoing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The low rows use faces (2,0,0); the high rows use (1,1,0). These are the forward tours in the original group-transport construction.

**Definition 1.4 (Backward face choices).**

$$\forall c \in Fin\left(4\right),\; \forall s \in Fin\left(3\right),\; incoming\left(c, s\right) = entry\left(((3, 1, 3), (3, 1, 3), (3, 2, 2), (3, 2, 2)), c, s\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.incoming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The low rows use faces (3,1,3); the high rows use (3,2,2). The two displayed faces are exactly those omitting neither ordered endpoint.

**Definition 1.5 (Source return words).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; returnWord\left(u, v, c\right) = entry\left((inverse\left(v\right) \times square\left(u\right), inverse\left(v\right) \times square\left(u\right), square\left(v\right) \times u, square\left(v\right) \times u), c\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.returnWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both low rows use ell = v inverse times u squared. Both high rows use h = v squared times u. Multiplication is the published right-action convention. After corner normalization the four oriented words are c1, inverse c3, c2, inverse c4; inverse directions are not silently renamed.

**Definition 1.6 (Phase offsets).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall s \in Fin\left(3\right),\; offset\left(u, v, c, s\right) = entry\left(((1, inverse\left(v\right), inverse\left(v\right) \times u), (1, inverse\left(v\right), inverse\left(v\right) \times u), (1, v, square\left(v\right)), (1, v, square\left(v\right))), c, s\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.offset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The low rows have offsets (1,v inverse,v inverse times u); the high rows have (1,v,v squared). These offsets specify actual sheets at each phase.

**Definition 1.7 (The three-phase permutation).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall y \in Omega \times Fin\left(3\right),\; apply\left(tour\left(u, v, c\right), y\right) = if\left(second\left(y\right) = 2, (act\left(first\left(y\right), returnWord\left(u, v, c\right)\right), 0), (first\left(y\right), add\left(second\left(y\right), 1\right))\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.tour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A tour state consists of a root sheet and a phase. The phase advances, and only the crossing from phase two to phase zero acts on the root by the return word. The inverse acts by the inverse word at phase zero. This tracks ordered endpoints, not a full transported frame.

**Definition 1.8 (Actual dart encoding).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall y \in Omega \times Fin\left(3\right),\; encode\left(u, v, c, y\right) = ((act\left(first\left(y\right), offset\left(u, v, c, second\left(y\right)\right)\right), corner\left(c, second\left(y\right)\right)), tip\left(c, second\left(y\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the phase offset to the root sheet and retain the ordered pair from the same row. The encoding is injective within each row. The actual guarded DartStep is proved equivalent to the image of the tour or its inverse.

**Definition 1.9 (Minimal return at the selected point).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; pointPeriod\left(u, v, c, x\right) = minimalPeriod\left(rightMultiply\left(returnWord\left(u, v, c\right)\right), x\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.pointPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The period is Function.minimalPeriod of right multiplication by the row's return word at the selected sheet. The component theorem assumes only that the acted-on set is finite; the group may be infinite, and the action may be nonfaithful, nonfree or nontransitive.

**Definition 1.10 (Finite indexed occurrences).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; \forall i \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right),\; occurrence\left(u, v, c, x, i\right) = encode\left(u, v, c, iterate\left(tour\left(u, v, c\right), i, (x, 0)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.occurrence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an index in Fin(3r), iterate the source-derived tour from phase zero and encode its actual dart. The proof derives the tour period 3r from the minimal point return r using pinned periodic-point lemmas.

**Theorem 1.11 (The complete actual component and its two generators).**

$$\forall G \in Group,\; \forall Omega \in RightAction\left(G\right),\; \forall u \in G,\; \forall v \in G,\; \forall c \in Fin\left(4\right),\; \forall x \in Omega,\; Finite\left(Omega\right) \Rightarrow \left(0 < pointPeriod\left(u, v, c, x\right) \land \left(Injective\left(occurrence\left(u, v, c, x\right)\right) \land \left(\left(\forall d \in Dart\left(Omega\right),\; DartRelated\left(u, v, encode\left(u, v, c, (x, 0)\right), d\right) \Leftrightarrow \left(\exists i \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right),\; occurrence\left(u, v, c, x, i\right) = d\right)\right) \land \left(\left(\forall j \in Fin\left(4\right),\; \forall k \in Fin\left(4\right),\; j \neq k \Leftrightarrow \left(\exists cs \in Fin\left(4\right) \times Fin\left(3\right),\; \left(corner\left(first\left(cs\right), second\left(cs\right)\right) = j \land tip\left(first\left(cs\right), second\left(cs\right)\right) = k\right) \land \left(\forall ds \in Fin\left(4\right) \times Fin\left(3\right),\; \left(corner\left(first\left(ds\right), second\left(ds\right)\right) = j \land tip\left(first\left(ds\right), second\left(ds\right)\right) = k\right) \Rightarrow ds = cs\right)\right)\right) \land \left(\left(\forall y \in Omega \times Fin\left(3\right),\; \forall d \in Dart\left(Omega\right),\; DartStep\left(u, v, encode\left(u, v, c, y\right), d\right) \Leftrightarrow \left(d = encode\left(u, v, c, apply\left(tour\left(u, v, c\right), y\right)\right) \lor d = encode\left(u, v, c, apply\left(inverse\left(tour\left(u, v, c\right)\right), y\right)\right)\right)\right) \land \left(minimalPeriod\left(tour\left(u, v, c\right), (x, 0)\right) = 3 \times pointPeriod\left(u, v, c, x\right) \land \left(\forall i \in Fin\left(3 \times pointPeriod\left(u, v, c, x\right)\right),\; occurrence\left(u, v, c, x, i\right) = encode\left(u, v, c, (iterate\left(rightMultiply\left(returnWord\left(u, v, c\right)\right), div\left(i, 3\right), x\right), mod\left(i, 3\right))\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.actual_component_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every row and every point of an arbitrary finite original right action, the period is positive, the Fin(3r) occurrence map is injective, and its image is the entire EqvGen component of the actual seed. The theorem also gives unique coverage of all twelve valid ordered endpoint types and the exact successor-or-predecessor characterization of every allowed generator.

The forward inclusion proves a source-specific invariant of the full original DartRelated chain: every intermediate remains encoded in the same row and in the same tour cycle. The converse constructs actual successor chains. Finite positivity, reduction modulo the minimal period and injectivity before return directly use Mathlib.Dynamics.PeriodicPts; the SameCycle API supplies natural iterate representatives.

No equation W to the r equals one is used. A singleton nonfaithful action has r equal to one and three occurrences, even though the complete transported frame can exchange the two complementary labels after those three crossings. Empty acted-on sets are covered by the point-quantified statement without an extra nonempty assumption.

The prerequisite ActualLinkCornerChains definitions supply the original face words, whole-face permutations, DartStep and DartRelated. This theorem concerns those combinatorial components. It does not establish the guarded affine Step correspondence with CyclicTriangleDisk seams, an origin normal form for the affine quotient, an open disk chart, the truncation-slice comparison, orientability or a global genus formula.

The source is the original group-transport section 122 and its supplemental 122.3 interface. Pinned Mathlib periodic-point and permutation-cycle declarations supply the generic orbit machinery. The newer FourColor orbit-list API is an advisory source with a different pin and is not imported. No literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.actual_component_enumeration`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.corner`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.encode`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.incoming`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.occurrence`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.offset`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.outgoing`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.pointPeriod`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.returnWord`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.tip`
- Truth anchor: `D5/S3/Geometry/Gluing/ActualCornerPointPeriods.tour`
- Dependency: [D5/S3/Geometry/Gluing/ActualLinkCornerChains](ActualLinkCornerChains.md)
