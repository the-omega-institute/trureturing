# Quandle Colorings of Algebraic Braid Closures

## Abstract

Quandle coloring spaces are preserved by both signed algebraic Markov stabilizations.

**Definition 1.1 (Boundary colorings).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.Colors`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.Colors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary coloring is a function from Fin n to an arbitrary rack Q. Neither finiteness nor quandle idempotence is assumed. At zero strands the coloring space consists of the unique empty function, including when Q itself is empty.

**Definition 1.2 (Artin action on rack colors).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.braidAction`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.braidAction` (`✓ std3`).

*Citation.* Roger Fenn; Colin Rourke (1992). *Racks and links in codimension two*. DOI: [10.1142/S0218216592000203](https://doi.org/10.1142/S0218216592000203). URL: <https://doi.org/10.1142/S0218216592000203>.

*Commentary.*

The local crossing sends (x,y) to (x ◃ y,x); its inverse sends (x,y) to (y,y ◃⁻¹ x). In an n-strand coloring these maps update only two adjacent coordinates. The existing local inverse and Yang–Baxter theorems supply the pair and three-coordinate identities. Disjoint coordinate updates commute, so the distant and adjacent Artin relators act trivially.

The resulting group homomorphism is defined on the existing literal n-strand Artin presentation, with values in permutations of the entire coloring space. It applies to infinite and empty racks as well as finite racks, and includes zero and one strands, which have no crossing generators. Multiplication applies the right factor first. No geometric braid identification or knot-closure theorem is asserted.

**Definition 1.3 (Final old coordinate).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.lastSlot`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.lastSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a strictly positive strand count n, the final old coordinate is the element n−1 of Fin n. The positivity hypothesis supplies a genuine coordinate for the stabilization formulas.

**Definition 1.4 (Closed boundary colorings).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.ClosedColorings`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.ClosedColorings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a rack Q and an element of the literal n-strand Artin group, a closed coloring is a function from Fin n to Q fixed by its braid transport.

**Definition 1.5 (Positive stabilization).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.positiveStabilizationEquiv`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.positiveStabilizationEquiv` (`✓ std3`).

*Citation.* Roger Fenn; Colin Rourke (1992). *Racks and links in codimension two*. DOI: [10.1142/S0218216592000203](https://doi.org/10.1142/S0218216592000203). URL: <https://doi.org/10.1142/S0218216592000203>.

*Commentary.*

For every quandle, every strictly positive strand count and every braid, positive stabilization preserves the entire coloring space. The forward map appends the old last color and the inverse restricts to the original coordinates. Comparing the last coordinate forces the appended color; idempotence removes the remaining crossing. The quandle may be infinite or empty.

**Definition 1.6 (Negative stabilization).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.negativeStabilizationEquiv`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.negativeStabilizationEquiv` (`✓ std3`).

*Citation.* Roger Fenn; Colin Rourke (1992). *Racks and links in codimension two*. DOI: [10.1142/S0218216592000203](https://doi.org/10.1142/S0218216592000203). URL: <https://doi.org/10.1142/S0218216592000203>.

*Commentary.*

Negative stabilization has the same diagonal extension and restriction maps. Its last coordinate equation uses the inverse rack action. Injectivity of that action and quandle idempotence force the added color to equal the old last color. Both inverse laws hold without a finiteness assumption.

**Definition 1.7 (Conjugation of closed braids).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.conjugationEquiv`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.conjugationEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport by a conjugating braid identifies the fixed-coloring spaces of a braid and its conjugate. The inverse uses transport by the inverse conjugating braid.

**Definition 1.8 (Coloring count).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.coloringCount`

*Formalization.* `D5/S3/Topology/QuandleMarkovColoring.coloringCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the natural cardinality of the closed-coloring type. It is an ordinary finite count when the color quandle is finite.

**Theorem 1.9 (Algebraic Markov invariance).**

Lean statement: `D5/S3/Topology/QuandleMarkovColoring.quandle_coloring_markov_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/QuandleMarkovColoring.quandle_coloring_markov_invariant` (`✓ std3`). ∎

*Citation.* Roger Fenn; Colin Rourke (1992). *Racks and links in codimension two*. DOI: [10.1142/S0218216592000203](https://doi.org/10.1142/S0218216592000203). URL: <https://doi.org/10.1142/S0218216592000203>.

*Commentary.*

For every finite quandle, any two positive-strand braids connected by a finite equivalence chain of conjugations and either signed Markov stabilization have equal coloring counts. The chain uses the existing Artin presentation, strand inclusion and signed last generators; products act by applying the right factor first.

The quandle assumption cannot in general be replaced by a rack assumption: on two colors, the constant-action rack whose every left translation swaps the colors has two colorings of the one-strand identity and no fixed colorings after either signed stabilization. Zero strands are excluded because there is no final old coordinate.

This is the classical algebraic coloring construction. A geometric identification of the algebraic Markov quotient with link closures is an additional theorem. The result asserts no such identification, classification of knots or new topological invariant.

## References

- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.ClosedColorings`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.Colors`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.braidAction`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.coloringCount`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.conjugationEquiv`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.lastSlot`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.negativeStabilizationEquiv`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.positiveStabilizationEquiv`
- Truth anchor: `D5/S3/Topology/QuandleMarkovColoring.quandle_coloring_markov_invariant`
- Dependency: [D5/S0/Certificates/Quandles/BraidColoringTransport](../../S0/Certificates/Quandles/BraidColoringTransport.md)
- Dependency: [D5/S3/Quantum/Algebra/Knot/WeightedPathArtinRepresentation](../Quantum/Algebra/Knot/WeightedPathArtinRepresentation.md)
