# Original execution on the joint native record

## Abstract

Original scanner and selector execution preserve the joint record and fee.

**Definition 1.1 (The original selector on native records).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.NativeExecute`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.NativeExecute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion uses the same selector, free reading, chronological archive, and finite fuel as original execution. A selected word appends its actual native endpoint and adds exactly one to a successful returned fee.

**Theorem 1.2 (Appending words to the original record).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.record_append`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.record_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least two, the record of an appended literal word is its native run from the original prefix record. The initial prefix and its actual tail are retained, including absorbing rejection.

**Theorem 1.3 (The original scalar endpoint).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.output_record`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.output_record` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original output is exactly the endpoint reading of the same original joint record for every positive k and literal word.

**Theorem 1.4 (Original and native selector execution agree).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.execute_same`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.execute_same` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least two, arbitrary selector, horizon, original literal prefix, free reading, and chronological archive, original execution equals native execution from that prefix record. The returned label and fee both agree.

**Theorem 1.5 (The joint record of a complete original history).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.record_history`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.record_history` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Flattening the same chronological AllowedBlock history gives exactly its native history record. This includes absorbing rejection and either original alphabet.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.NativeExecute`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.execute_same`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.output_record`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.record_append`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge.record_history`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NarrowWindowCost](NarrowWindowCost.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciIrreversibleAcquisition](../KBonacciIrreversibleAcquisition.md)
