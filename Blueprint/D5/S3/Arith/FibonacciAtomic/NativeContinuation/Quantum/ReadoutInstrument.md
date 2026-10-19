# Native high-window readout instrument

## Abstract

A bounded native FIB continuation is represented by a diagonal quantum instrument.

This module fixes the five initialized native windows in the foundational order (0,2,3,5,25), reads one first window, and appends the native high window (the label 5 continuation). The source basis is a finite current-state encoding. The acquired outcome keeps the first quantity parity together with the actual reply; action history, source ancestry and actual tree leaves remain external.

The two sources whose first seam is one are rejected by the high-window guard. The rejection is an absorbing output branch and is retained in the total table. The matrix family has one Kraus column per source and one output coordinate for each of the three live successors plus the absorbing rejection coordinate.

**Theorem 1.1 (Exact native continuation table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.native_reply_table`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.native_reply_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each of the five source indices, the existing raw reader evaluated on the source window followed by high returns the displayed replies 5, rejection, 18, 26, rejection. This is a direct finite computation from rawTransition and rawOutput; it does not introduce a second reader or identify a tree leaf with a window label.

**Theorem 1.2 (Diagonal branch factorization and hidden joint mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.diagonal_readout_consumer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.diagonal_readout_consumer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real diagonal source law p, the branch with acquired parity odd and rejection has mass p(25), the hidden joint coordinate kappa. The same theorem records the diagonal Kraus factorization for that branch, using the complete finite family and aggregate column Gram orthogonality. Branch matrices are unnormalized; no conditional state is assigned to a zero-mass branch.

**Theorem 1.3 (Born trace of the hidden-joint branch).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.branch_trace_is_hidden_joint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.branch_trace_is_hidden_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of the concrete branch state on a diagonal input is exactly the real mass p(25), embedded in the complex scalars. This is a branch trace identity for the stipulated finite instrument, not a claim of physical preparation, coherence control, unrestricted CPTP dynamics, or a Fock-space realization.

The generic diagonal Kraus theorem supplies completeness, nonnegative weights, the channel obtained by summing branches, and the factorization criterion. This FIB application consumes those results at one actual continuation and stops there: it does not add a generic quantum wrapper, put provenance in the density matrix, or transport the result to arbitrary acquired tree histories.

Dependencies: the existing ImmediateWindowStateCapacity reader and the JointLaw native continuation semantics, together with the frozen diagonal Kraus factorization.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.branch_trace_is_hidden_joint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.diagonal_readout_consumer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.native_reply_table`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw](../JointLaw.md)
- Dependency: [D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization](../../../../Quantum/Measurement/DiagonalKrausInstrumentFactorization.md)
