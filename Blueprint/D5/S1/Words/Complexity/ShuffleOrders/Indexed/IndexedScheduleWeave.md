# IndexedScheduleWeave

## Abstract

Selected indexed traces can be refilled monotonically in fixed positions.

This module iterates the binary fixed-source promotion theorem over a list of factors. Schedule labels are source positions, not factor values, so repeated equal factors and repeated letters retain distinct identities.

**Theorem 1.1 (Successful option traversal preserves length).**

$$\forall read,entries,word,\operatorname{mapM}\left(entries, read\right) = \operatorname{some}\left(word\right)\Rightarrow\operatorname{length}\left(word\right) = \operatorname{length}\left(entries\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleWeave.mapM_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For any read : B->Option A, entries, and word, entries.mapM read=some word implies word.length=entries.length.

## References

- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleWeave.mapM_length`
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder](IndexedScheduleOrder.md)
