# BinaryScheduleOrder

## Abstract

Binary schedules track ordered occurrences from two fixed sources.

The source paper uses shuffle products and retains their alignment multiplicities. This repository module supplies the fixed-source occurrence bookkeeping needed later: equal letters and duplicate source factors are never identified.

**Definition 1.1 (Two source labels).**

$$Side$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.Side` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Side is the two-constructor type first|second, with decidable equality; it records which unchanged source supplies each scheduled position.

**Definition 1.2 (Occurrence annotation with offsets).**

$$annotateTwoFrom$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.annotateTwoFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Given initial occurrence counters for both sides and a Side list, annotateTwoFrom labels every schedule entry by its zero-based occurrence number within that side and increments only the selected counter.

**Definition 1.3 (Zero-based occurrence annotation).**

$$annotateTwo$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.annotateTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

annotateTwo starts annotateTwoFrom at counter zero for both sources.

**Definition 1.4 (Shift occurrence coordinates).**

$$shiftPairOccurrences$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.shiftPairOccurrences` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

shiftPairOccurrences firstOffset secondOffset adds the matching offset to an annotated first or second occurrence without changing its side.

**Theorem 1.5 (Offset naturality).**

$$annotateTwoFromadd$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.annotateTwoFrom_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For all offsets, schedules, and starting counters, annotation from offset starts equals mapping shiftPairOccurrences over annotation from the unshifted starts.

## References

- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.Side`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.annotateTwo`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.annotateTwoFrom`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.annotateTwoFrom_add`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder.shiftPairOccurrences`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading](../../LyndonBrackets/LyndonBracketLeading.md)
