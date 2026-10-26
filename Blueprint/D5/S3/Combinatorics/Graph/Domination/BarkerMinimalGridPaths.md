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

**Theorem 1.3 (fullStep eq mulVec).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.fullStep_eq_mulVec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.fullStep_eq_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full integer vector v, fullStep v equals transition.mulVec v. Injectivity of append identifies accepted masks with admitted unit-weight successors.

**Theorem 1.4 (fullOrbit matrix).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.fullOrbit_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.fullOrbit_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, fullOrbit k is the action of transition raised to k on the terminal vector. The proof applies the pinned matrix multiplication action laws.

**Definition 1.5 (trace).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.trace`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.trace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The start and each successive appended mask determine the entire ordered full-state path.

**Theorem 1.6 (trace unique).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.trace_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.trace_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, state s, suffix word w and state path p with the prescribed start and append equations, p equals trace k s w. No witness choices or symmetry quotients enter the path.

**Definition 1.7 (expanded).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expanded`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expanded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Signed coordinates −2,−1,0,1 read the four history columns; the supplied suffix supplies successive real masks, and subsequent columns are absent.

**Definition 1.8 (expandedWindow).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expandedWindow`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expandedWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five symbols centred at a nonnegative coordinate are read from the history-and-suffix stream.

**Theorem 1.9 (runWeight iff tests).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight_iff_tests`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight_iff_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, full state s and suffix w, runWeight k s w equals one exactly when every centre in Fin(k+2) satisfies the corresponding Local window test. The base k=0 is precisely the two terminal checks.

**Definition 1.10 (start).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.start`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.start` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two labelled real masks a,b encode the full start state 8*a+b in the first block.

**Theorem 1.11 (accepted cons iff).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.accepted_cons_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.accepted_cons_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every suffix length k, masks a,b and suffix w, the concatenated numeric word belongs to acceptedWords(k+2) exactly when its unique run from start a b has weight one.

**Theorem 1.12 (actualCount fullOrbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.actualCount_fullOrbit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.actualCount_fullOrbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, the actual inclusion-minimal dominating subset count of the ordinary open grid of width k+2, cast to the integers, equals the sum of fullOrbit k over all 64 starts. This includes width two with no transitions.

This is internal Stage A work. The unchanged whole actual-subset generating-series endpoint requires every counting and quotient interface to be compiled; no resolution or admission follows from a partial interface.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.accepted_cons_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.actualCount_fullOrbit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expanded`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.expandedWindow`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.fullOrbit_matrix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.fullStep_eq_mulVec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.runWeight_iff_tests`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.start`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.sum_runWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.trace`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths.trace_unique`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer](BarkerMinimalGridTransfer.md)
