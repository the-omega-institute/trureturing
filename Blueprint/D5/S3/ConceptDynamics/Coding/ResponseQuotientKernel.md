# Response quotient kernels

## Abstract

Actual numbered finite path lifts define a response kernel; depth zero remembers the state and increasing depth can only forget information.

**Theorem 1.1 (Finite path responses are nested).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseQuotientKernel.response_zero_and_step`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseQuotientKernel.response_zero_and_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A numbered finite path is lifted from its terminal state by the actual incoming edge map. The resulting response readout records the projected state and every lifted path endpoint. At depth zero, the empty path recovers the original state exactly. Extending a path by one edge only adds coordinates computed from the previous readout, so equality at depth d implies equality at depth d+1.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseQuotientKernel.response_zero_and_step`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap](CountedMatrixOverlap.md)
