# Fixed-Source Binary Shuffle Order

## Abstract

Occurrence-indexed binary schedules can be promoted to start at the larger fixed source without decreasing their evaluated word.

The source paper uses shuffle products and retains their alignment multiplicities. This repository module supplies the fixed-source occurrence bookkeeping needed later: equal letters and duplicate source factors are never identified.

**Definition 1.1 (Two source labels).**

$$Side$$

*Formalization.* `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.Side` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Side is the two-constructor type first|second, with decidable equality; it records which unchanged source supplies each scheduled position.

**Definition 1.2 (Occurrence annotation with offsets).**

$$annotateTwoFrom$$

*Formalization.* `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.annotateTwoFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

Given initial occurrence counters for both sides and a Side list, annotateTwoFrom labels every schedule entry by its zero-based occurrence number within that side and increments only the selected counter.

**Definition 1.3 (Zero-based occurrence annotation).**

$$annotateTwo$$

*Formalization.* `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.annotateTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

annotateTwo starts annotateTwoFrom at counter zero for both sources.

**Definition 1.4 (Shift occurrence coordinates).**

$$shiftPairOccurrences$$

*Formalization.* `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.shiftPairOccurrences` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

shiftPairOccurrences firstOffset secondOffset adds the matching offset to an annotated first or second occurrence without changing its side.

**Theorem 1.5 (Offset naturality).**

$$annotateTwoFromadd$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.annotateTwoFrom_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For all offsets, schedules, and starting counters, annotation from offset starts equals mapping shiftPairOccurrences over annotation from the unshifted starts.

**Definition 1.6 (Read an annotated binary occurrence).**

$$readTwo$$

*Formalization.* `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.readTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

readTwo first second reads index i from the source selected by Side and returns Option A, preserving the occurrence coordinate.

**Definition 1.7 (Evaluate a fixed-source schedule).**

$$evaluateTwo$$

*Formalization.* `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.evaluateTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

evaluateTwo maps occurrence annotation through readTwo and sequences the options; the source words are never permuted or replaced.

**Definition 1.8 (Consume each source exactly once).**

$$ValidTwoSchedule$$

*Formalization.* `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.ValidTwoSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

A binary schedule is valid for first and second exactly when its counts of Side.first and Side.second equal the respective source lengths.

**Theorem 1.9 (Promote the larger source to the front).**

$$fixedSourcefrontPromotion$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.fixedSource_frontPromotion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For linearly ordered A, fixed words first>=second, a valid schedule starting with second, and a successful evaluation word, there exist a valid promoted schedule starting with first and an evaluated promotedWord with word<=promotedWord. Both source words and every occurrence are retained.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.Side`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.ValidTwoSchedule`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.annotateTwo`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.annotateTwoFrom`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.annotateTwoFrom_add`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.evaluateTwo`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.fixedSource_frontPromotion`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.readTwo`
- Truth anchor: `D5/S1/Words/Complexity/LyndonShuffleScheduleOrder.shiftPairOccurrences`
- Dependency: [D5/S1/Words/Complexity/LyndonStandardBracket](LyndonStandardBracket.md)
