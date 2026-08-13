# Cyclic Window Revival

## Abstract

A full loop restores both generators of a finite cyclic observer window.

**Theorem 1.1 (Cyclic window generators recur after one full loop).**

$$S^{M} = 1 \land C^{M} = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/CyclicWindowRevival.cyclic_window_generators_recur` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite observer window of size M, the address shift and phase clock each return to the identity after M updates. Together these recurrences certify perfect revival after a full cyclic loop. This statement is confined to the cyclic branch and does not claim a classification of revival scores in other branches.

## References

- Truth anchor: `D5/S3/ObserverMemory/CyclicWindowRevival.cyclic_window_generators_recur`
- Dependency: [D5/S3/Observer/WindowRegister](../Observer/WindowRegister.md)
