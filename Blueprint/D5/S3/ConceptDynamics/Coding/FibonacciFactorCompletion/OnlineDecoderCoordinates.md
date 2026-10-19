# Exact coordinates of grouped Fibonacci sources

## Abstract

The supported affine coordinates of every OperationOmega source equal the series of its grouped legal digits.

**Theorem 1.1 (Grouped legal digits and guard path).**

$$\forall a \in Nat \to Label, x \in Nat \to Real,\; \operatorname{OperationOmega}\left(a, x\right) \Rightarrow \left(\exists d \in LegalDigits, path \in Nat \to Guard,\; \operatorname{apply}\left(path, 0\right) = G0 \land \left(\left(\forall p \in Nat,\; \operatorname{nextGuard}\left(\operatorname{apply}\left(path, p\right), \operatorname{apply}\left(a, p\right)\right) = \operatorname{some}\left(\operatorname{apply}\left(path, \operatorname{add}\left(p, 1\right)\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{window}\left(d, p\right) = \operatorname{labelWindow}\left(\operatorname{apply}\left(a, p\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{actualGuard}\left(\operatorname{false}\left(\right), d, p\right) = \operatorname{guardBool}\left(\operatorname{apply}\left(path, p\right)\right)\right) \land \left(\left(\forall p \in Nat,\; \operatorname{apply}\left(x, p\right) \in \operatorname{stateInterval}\left(\operatorname{guardBool}\left(\operatorname{apply}\left(path, p\right)\right)\right)\right) \land \left(\forall p \in Nat,\; \operatorname{apply}\left(x, p\right) = \operatorname{branch}\left(\operatorname{labelWindow}\left(\operatorname{apply}\left(a, p\right)\right), \operatorname{apply}\left(x, \operatorname{add}\left(p, 1\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_digit_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary label and coordinate streams satisfying the original OperationOmega predicate, the declaration constructs one legal Boolean stream and a guard path. The five Coding labels are mapped to the low-to-high S1 windows 000, 010, 100, 001 and 101. The construction proves grouped window equality, the cross-block no-adjacent-one condition, agreement of the incoming guard with the previous block's highest bit, and transport of the original support interval to the S1 guard interval. It also proves the affine branch after normalizing the two definitions of the reciprocal golden ratio and the identity t cubed equals 2t minus 1.

The declaration supplies a source correspondence and a scalar recurrence in the S1 branch model. It does not identify the supplied coordinate stream with the S1 kappa series, and it does not construct an observation record or an online decoder.

**Theorem 1.2 (Finite Coding tails are finite S1 tails).**

$$\forall a \in Nat \to Label, d \in LegalDigits,\; \left(\forall p \in Nat,\; \operatorname{window}\left(d, p\right) = \operatorname{labelWindow}\left(\operatorname{apply}\left(a, p\right)\right)\right) \Rightarrow \left(\operatorname{OperationFiniteSource}\left(a\right) \Leftrightarrow \operatorname{finiteTail}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_finite_source_iff_of_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any legal digit stream whose grouped windows match the given label stream is eventually zero exactly when the label stream is eventually the empty-window label. The explicit window hypothesis identifies that same digit stream. Both directions use the exact three-to-one block index arithmetic; no separate coordinate or OperationOmega premise is required.

The finite-tail statement does not assert finiteTail for arbitrary OperationOmega paths, and it does not transport OperationRecord, observe, ErrorBound or closed candidate ownership.

**Theorem 1.3 (One digit stream realizes every original coordinate).**

$$\forall a \in Nat \to Label, x \in Nat \to Real,\; \operatorname{OperationOmega}\left(a, x\right) \Rightarrow \left(\exists d \in LegalDigits,\; \left(\forall p \in Nat,\; \operatorname{window}\left(d, p\right) = \operatorname{labelWindow}\left(a\left(p\right)\right)\right) \land \left(\left(\forall p \in Nat,\; x\left(p\right) = \operatorname{kappa}\left(\operatorname{bitShift}\left(d, 3 \cdot p\right)\right)\right) \land \left(\operatorname{OperationFiniteSource}\left(a\right) \Leftrightarrow \operatorname{finiteTail}\left(d\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_coordinate_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OperationOmega supplies a legal guard path, guard-dependent bounded coordinates, and the original affine recurrence. At each position the grouped digit window is exactly the prescribed label window. Its kappa series obeys the same recurrence, and both coordinate streams stay in the common bounded support. After n further windows, their difference equals the later difference multiplied by the nth power of negative g. The later difference has absolute value at most four; since zero is less than g and g is less than one, the initial difference is zero. This applies at every position p to the same digit stream. The explicit window equality also transfers eventual empty labels to eventual zero digits and conversely, so the coordinate and finite-tail conclusions concern that same stream.

The theorem allows every OperationOmega source, including sources that are not eventually empty. The deletion index is exactly three times p individual bits. It does not supply the converse construction from arbitrary legal digits, observation or error transport, finite certification of all closed candidates, or a streaming decoder and storage bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_coordinate_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_digit_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.operation_finite_source_iff_of_bridge`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationCommonTailWidth](../../../../S1/Digit/Infinite/ClosedObservationCommonTailWidth.md)
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](../../../../S1/Digit/Infinite/ClosedObservationGraphRealization.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Operations](Operations.md)
