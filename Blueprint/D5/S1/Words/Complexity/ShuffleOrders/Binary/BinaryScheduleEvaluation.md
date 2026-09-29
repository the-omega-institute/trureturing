# BinaryScheduleEvaluation

## Abstract

Binary schedule evaluation compares swapped fixed-source prefixes.

The source paper uses shuffle products and retains their alignment multiplicities. This repository module supplies the fixed-source occurrence bookkeeping needed later: equal letters and duplicate source factors are never identified.

**Definition 1.1 (Read an annotated binary occurrence).**

$$\forall first,second,i, \operatorname{readTwo}\left(first, second, \operatorname{pair}\left(firstSide, i\right)\right) = \operatorname{getOptional}\left(first, i\right)\land\operatorname{readTwo}\left(first, second, \operatorname{pair}\left(secondSide, i\right)\right) = \operatorname{getOptional}\left(second, i\right)$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation.readTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

readTwo first second reads index i from the source selected by Side and returns Option A, preserving the occurrence coordinate.

**Definition 1.2 (Evaluate a fixed-source schedule).**

$$\forall first,second,schedule, \operatorname{evaluateTwo}\left(first, second, schedule\right) = \operatorname{mapM}\left(\operatorname{annotateTwo}\left(schedule\right), \operatorname{readTwo}\left(first, second\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation.evaluateTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

evaluateTwo maps occurrence annotation through readTwo and sequences the options; the source words are never permuted or replaced.

**Definition 1.3 (Consume each source exactly once).**

$$\forall first,second,schedule, \operatorname{ValidTwoSchedule}\left(first, second, schedule\right)\iff\operatorname{count}\left(schedule, firstSide\right) = \operatorname{length}\left(first\right)\land\operatorname{count}\left(schedule, secondSide\right) = \operatorname{length}\left(second\right)$$

*Formalization.* `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation.ValidTwoSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

A binary schedule is valid for first and second exactly when its counts of Side.first and Side.second equal the respective source lengths.

## References

- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation.ValidTwoSchedule`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation.evaluateTwo`
- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation.readTwo`
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder](BinaryScheduleOrder.md)
