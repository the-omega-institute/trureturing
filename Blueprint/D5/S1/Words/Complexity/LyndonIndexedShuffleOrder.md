# Occurrence-Indexed Lyndon Shuffle Order

## Abstract

Every occurrence-indexed interleaving of nonincreasing Lyndon factors is lexicographically bounded by their ordered concatenation.

This module iterates the binary fixed-source promotion theorem over a list of factors. Schedule labels are source positions, not factor values, so repeated equal factors and repeated letters retain distinct identities.

**Definition 1.1 (Indexed source schedules).**

$$IndexedSchedule$$

*Formalization.* `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.IndexedSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

IndexedSchedule abbreviates List Nat; each entry names a position in the factor list and therefore distinguishes duplicate factors.

**Definition 1.2 (Exact occurrence consumption).**

$$IsValidSchedule$$

*Formalization.* `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.IsValidSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For factors : List (List A), a schedule is valid when, for every natural source index i, schedule.count i equals the length of factors.getD i []. This excludes out-of-range labels and consumes every source occurrence exactly once.

**Definition 1.3 (Annotate indexed occurrences).**

$$annotateIndexedFrom$$

*Formalization.* `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.annotateIndexedFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Starting from a counter function used : Nat->Nat, annotateIndexedFrom replaces each source label i by (i,used i) and increments only the counter at i.

**Definition 1.4 (Zero-based indexed annotation).**

$$annotateIndexed$$

*Formalization.* `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.annotateIndexed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

annotateIndexed starts every source counter at zero.

**Definition 1.5 (Read a fixed indexed occurrence).**

$$readIndexed$$

*Formalization.* `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.readIndexed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

readIndexed factors (i,j) reads occurrence j from factors.getD i [] and returns Option A.

**Definition 1.6 (Evaluate a valid indexed schedule).**

$$evaluateSchedule$$

*Formalization.* `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.evaluateSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

evaluateSchedule returns none unless IsValidSchedule holds; otherwise it maps all annotated occurrences through readIndexed and sequences the result.

**Theorem 1.7 (Successful option traversal preserves length).**

$$mapMlength$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.mapM_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For any read : B->Option A, entries, and word, entries.mapM read=some word implies word.length=entries.length.

**Theorem 1.8 (Ordered Lyndon concatenation is maximal).**

$$evaluateScheduleleflatten$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.evaluateSchedule_le_flatten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For linearly ordered A, Lyndon factors in pairwise nonincreasing order, a valid indexed schedule, and successful evaluation word, one has word<=factors.flatten. The proof promotes the leading factor occurrence by occurrence and never collapses duplicate factor identities.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.IndexedSchedule`
- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.IsValidSchedule`
- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.annotateIndexed`
- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.annotateIndexedFrom`
- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.evaluateSchedule`
- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.evaluateSchedule_le_flatten`
- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.mapM_length`
- Truth anchor: `D5/S1/Words/Complexity/LyndonIndexedShuffleOrder.readIndexed`
- Dependency: [D5/S1/Words/Complexity/LyndonShuffleScheduleOrder](LyndonShuffleScheduleOrder.md)
