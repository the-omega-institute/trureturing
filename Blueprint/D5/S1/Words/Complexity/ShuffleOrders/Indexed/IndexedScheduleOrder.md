# IndexedScheduleOrder

## Abstract

Indexed schedules preserve every occurrence of every fixed source.

This module iterates the binary fixed-source promotion theorem over a list of factors. Schedule labels are source positions, not factor values, so repeated equal factors and repeated letters retain distinct identities.

**Definition 1.1 (Indexed source schedules).**

$$IndexedSchedule$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.IndexedSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

IndexedSchedule abbreviates List Nat; each entry names a position in the factor list and therefore distinguishes duplicate factors.

**Definition 1.2 (Exact occurrence consumption).**

$$IsValidSchedule$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.IsValidSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For factors : List (List A), a schedule is valid when, for every natural source index i, schedule.count i equals the length of factors.getD i []. This excludes out-of-range labels and consumes every source occurrence exactly once.

**Definition 1.3 (Annotate indexed occurrences).**

$$annotateIndexedFrom$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.annotateIndexedFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Starting from a counter function used : Nat->Nat, annotateIndexedFrom replaces each source label i by (i,used i) and increments only the counter at i.

**Definition 1.4 (Zero-based indexed annotation).**

$$annotateIndexed$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.annotateIndexed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

annotateIndexed starts every source counter at zero.

**Definition 1.5 (Read a fixed indexed occurrence).**

$$readIndexed$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.readIndexed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

readIndexed factors (i,j) reads occurrence j from factors.getD i [] and returns Option A.

**Definition 1.6 (Evaluate a valid indexed schedule).**

$$evaluateSchedule$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.evaluateSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

evaluateSchedule returns none unless IsValidSchedule holds; otherwise it maps all annotated occurrences through readIndexed and sequences the result.

## References

- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.IndexedSchedule`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.IsValidSchedule`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.annotateIndexed`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.annotateIndexedFrom`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.evaluateSchedule`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder.readIndexed`
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder](../Binary/BinaryScheduleOrder.md)
