# Original common-tail selectors and informative endpoints

## Abstract

Original common-tail selectors and informative endpoints

**Definition 1.1 (Informative endpoints in a paid interval).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression.count`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count retains endpoints whose issued index is divisible by the selected cadence. Every complete word remains paid, including endpoints omitted from the compressed transcript.

**Theorem 1.2 (Compression from an arbitrary original archive).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression.compress`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression.compress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary k at least two, block width, selector, remembered INITIAL reading, phase family and starting archive, correct execution on a common current scalar and tail produces a binary protocol with one query per potentially informative endpoint. The retained INITIAL target may repeat. The cadence hypothesis states that every literal word has zero increment at omitted endpoints. At each successful response child the scalar and tail are again common. A uniformly rejecting word gives one absorbing future archive and can only serve a homogeneous target. Stops at any endpoint, zero waits, padding and repairs remain in the original execution and its paid horizon.

Cadence one keeps every successful binary endpoint and requires no silence premise. Larger cadences retain the repeated-guardrail application, with its original public statement and paid fee. The remembered INITIAL reading is independent of the current scalar; an acquired prefix need not be empty or share its current scalar with that reading.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression.compress`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalCommonTailCompression.count`
- Dependency: [D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound](../../../Observer/Budget/WorstCaseDepthInformationLowerBound.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost](OriginalNarrowCost.md)
