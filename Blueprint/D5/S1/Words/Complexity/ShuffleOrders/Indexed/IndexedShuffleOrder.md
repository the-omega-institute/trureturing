# IndexedShuffleOrder

## Abstract

Indexed Lyndon schedule evaluation is bounded by factor concatenation.

This module iterates the binary fixed-source promotion theorem over a list of factors. Schedule labels are source positions, not factor values, so repeated equal factors and repeated letters retain distinct identities.

**Theorem 1.1 (Ordered Lyndon concatenation is maximal).**

$$\forall factors,schedule,word, (\forall u\in factors,\operatorname{IsLyndon}\left(u\right))\land\operatorname{Pairwise}\left(factors, \operatorname{lambda}\left(u, v, u\geq v\right)\right)\land\operatorname{IsValidSchedule}\left(factors, schedule\right)\land\operatorname{evaluateSchedule}\left(factors, schedule\right) = \operatorname{some}\left(word\right)\Rightarrow word\leq\operatorname{flatten}\left(factors\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedShuffleOrder.evaluateSchedule_le_flatten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For linearly ordered A, Lyndon factors in pairwise nonincreasing order, a valid indexed schedule, and successful evaluation word, one has word<=factors.flatten. The proof promotes the leading factor occurrence by occurrence and never collapses duplicate factor identities.

## References

- Truth anchor: `D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedShuffleOrder.evaluateSchedule_le_flatten`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder](../../LyndonBrackets/LyndonOrder.md)
- Dependency: [D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedSchedulePromotion](IndexedSchedulePromotion.md)
