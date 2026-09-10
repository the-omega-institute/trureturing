# A Concrete Squared-Residual Cover

## Abstract

A rational box forest confines a real squared-residual sublevel to its central interval.

**Definition 1.1 (Five postordered rational intervals).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareBoxes`

*Formalization.* `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareBoxes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nodes 0 through 4 have intervals [-2,-1], [1,2], [-1,1], [-1,2], and [-2,2], respectively. Each box has one coordinate; node 4 is the root.

**Definition 1.2 (The central target interval).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareTargets`

*Formalization.* `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareTargets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is one target box, with rational endpoints -1 and 1.

**Definition 1.3 (The square of the real coordinate).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareResidual`

*Formalization.* `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareResidual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The single residual expression squares input coordinate 0. Its input annotations are [-2,2], and its output annotations are [0,4]. Its real evaluation is x squared.

**Definition 1.4 (Two exclusions, one covered leaf, and two splits).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareForest`

*Formalization.* `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareForest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nodes 0 and 1 enclose the squared residual in [1,4] on their respective outer intervals. Node 2 enters target 0. Node 3 splits at 1 into nodes 2 and 1; node 4 splits at -1 into nodes 0 and 3. Both children precede each parent, and the split halves are closed.

**Theorem 1.5 (Exact acceptance at tolerance one quarter).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.square_forest_accepted`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/BoxCoverExamples.square_forest_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction proves that checkForest returns true for squareBoxes, squareTargets, squareResidual, tolerance 1/4, and squareForest. In particular, each excluded leaf has lower bound 1 strictly above 1/4.

**Theorem 1.6 (The real sublevel stays in the central interval).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.square_sublevel_covered`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/BoxCoverExamples.square_sublevel_covered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The set of real x in [-2,2] with absolute value of x squared at most 1/4 is contained in [-1,1]. The proof applies checked_forest_covers_sublevel to square_forest_accepted at root 4, then evaluates the single coordinate and target. The conclusion concerns all real points of this nonempty sublevel.

**Definition 1.7 (A proposed point outside the target).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.escapedSublevelClaim`

*Formalization.* `D5/S0/Certificates/BoxCover/BoxCoverExamples.escapedSublevelClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim asserts that some real x belongs to [-2,2], satisfies the squared-residual bound 1/4, and does not belong to [-1,1].

**Theorem 1.8 (No sublevel point escapes).**

Lean statement: `D5/S0/Certificates/BoxCover/BoxCoverExamples.no_escaped_sublevel`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BoxCover/BoxCoverExamples.no_escaped_sublevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The claim is false: square_sublevel_covered places every proposed witness in [-1,1], contradicting its asserted nonmembership.

## References

- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.escapedSublevelClaim`
- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.no_escaped_sublevel`
- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareBoxes`
- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareForest`
- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareResidual`
- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.squareTargets`
- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.square_forest_accepted`
- Truth anchor: `D5/S0/Certificates/BoxCover/BoxCoverExamples.square_sublevel_covered`
- Dependency: [D5/S0/Certificates/BoxCover/CheckedRationalBoxCover](CheckedRationalBoxCover.md)
