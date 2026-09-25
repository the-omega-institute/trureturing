# BinaryFrontPromotion

## Abstract

A smaller leading source can be promoted without decreasing evaluation.

The source paper uses shuffle products and retains their alignment multiplicities. This repository module supplies the fixed-source occurrence bookkeeping needed later: equal letters and duplicate source factors are never identified.

**Theorem 1.1 (Promote the larger source to the front).**

$$\forall first,second,schedule,word, second\leq first\land\operatorname{ValidTwoSchedule}\left(first, second, schedule\right)\land\operatorname{headOptional}\left(schedule\right) = \operatorname{some}\left(secondSide\right)\land\operatorname{evaluateTwo}\left(first, second, schedule\right) = \operatorname{some}\left(word\right)\Rightarrow\exists promotedSchedule,promotedWord, \operatorname{ValidTwoSchedule}\left(first, second, promotedSchedule\right)\land\operatorname{headOptional}\left(promotedSchedule\right) = \operatorname{some}\left(firstSide\right)\land\operatorname{evaluateTwo}\left(first, second, promotedSchedule\right) = \operatorname{some}\left(promotedWord\right)\land word\leq promotedWord$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryFrontPromotion.fixedSource_frontPromotion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For linearly ordered A, fixed words first>=second, a valid schedule starting with second, and a successful evaluation word, there exist a valid promoted schedule starting with first and an evaluated promotedWord with word<=promotedWord. Both source words and every occurrence are retained.

## References

- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryFrontPromotion.fixedSource_frontPromotion`
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation](BinaryScheduleEvaluation.md)
