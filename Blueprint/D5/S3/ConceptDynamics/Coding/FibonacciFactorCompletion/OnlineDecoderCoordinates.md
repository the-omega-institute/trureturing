# Exact coordinates of grouped Fibonacci sources

## Abstract

The supported affine coordinates of every OperationOmega source equal the series of its grouped legal digits.

**Theorem 1.1 (One digit stream realizes every original coordinate).**

$$\forall a \in Nat \to Label, x \in Nat \to Real,\; \operatorname{OperationOmega}\left(a, x\right) \Rightarrow \left(\exists d \in LegalDigits,\; \left(\forall p \in Nat,\; \operatorname{window}\left(d, p\right) = \operatorname{labelWindow}\left(a\left(p\right)\right)\right) \land \left(\forall p \in Nat,\; x\left(p\right) = \operatorname{kappa}\left(\operatorname{bitShift}\left(d, 3 \cdot p\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_coordinate_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OperationOmega supplies a legal guard path, guard-dependent bounded coordinates, and the original affine recurrence. At each position the grouped digit window is exactly the prescribed label window. Its kappa series obeys the same recurrence, and both coordinate streams stay in the common bounded support. After n further windows, their difference equals the later difference multiplied by the nth power of negative g. The later difference has absolute value at most four; since zero is less than g and g is less than one, the initial difference is zero. This applies at every position p to the same digit stream.

The theorem allows every OperationOmega source, including sources that are not eventually empty. The deletion index is exactly three times p individual bits. It does not supply the converse construction from arbitrary legal digits, observation or error transport, finite certification of all closed candidates, or a streaming decoder and storage bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_coordinate_bridge`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth](../../../../S1/Digit/Infinite/ClosedObservationCommonTailWidth.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderBridge](OnlineDecoderBridge.md)
