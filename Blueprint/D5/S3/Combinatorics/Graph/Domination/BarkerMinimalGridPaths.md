# Exact numeric-word and all-length full-state counting

## Abstract

Exact numeric-word and all-length full-state counting

**Definition 1.1 (runWeight).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An appended-mask word receives the product of its accepted transition indicators and its full terminal weight. It is always zero or one.

**Theorem 1.2 (sum runWeight).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.sum_runWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.sum_runWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every suffix length k and every full state s, summing runWeight k s over every Fin k → Fin 8 word is exactly fullOrbit k s. The first-mask function equivalence supplies the induction.

**Definition 1.3 (expanded).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expanded`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expanded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Signed coordinates −2,−1,0,1 read the four history columns; the supplied suffix supplies successive real masks, and subsequent columns are absent.

**Definition 1.4 (expandedWindow).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expandedWindow`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expandedWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five symbols centred at a nonnegative coordinate are read from the history-and-suffix stream.

**Theorem 1.5 (runWeight iff tests).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight_iff_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight_iff_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, full state s and suffix w, runWeight k s w equals one exactly when every centre in Fin(k+2) satisfies the corresponding Local window test. The base k=0 is precisely the two terminal checks.

**Definition 1.6 (start).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.start`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.start` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two labelled real masks a,b encode the full start state 8*a+b in the first block.

**Theorem 1.7 (accepted cons iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.accepted_cons_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.accepted_cons_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every suffix length k, masks a,b and suffix w, the concatenated numeric word belongs to acceptedWords(k+2) exactly when its unique run from start a b has weight one.

**Theorem 1.8 (actualCount fullOrbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.actualCount_fullOrbit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.actualCount_fullOrbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, the actual inclusion-minimal dominating subset count of the ordinary open grid of width k+2, cast to the integers, equals the sum of fullOrbit k over all 64 starts. This includes width two with no transitions.

The generic CycleItalianDominationRecurrence.sum_pathWeight sums arbitrary intermediate states between fixed endpoints u and v for n+1 edges. At a positive suffix length k its parameters would be the state type Fin 4672, the unit admitted-edge matrix M, and n=k−1, followed by a terminal-weighted endpoint sum and a mask-word correspondence. The argument here defines each continuation by append and identifies its weight with the actual local tests for every k, including zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.accepted_cons_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.actualCount_fullOrbit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expanded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expandedWindow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight_iff_tests`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.start`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.sum_runWeight`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer](BarkerMinimalGridTransfer.md)
