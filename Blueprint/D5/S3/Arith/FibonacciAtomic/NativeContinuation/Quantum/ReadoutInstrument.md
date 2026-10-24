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

The stipulated matrices also determine every branch on arbitrary complex inputs. In zero-based source coordinates i = 0,1,2,3,4, the complete outcome codes are 0,3,5,6,7 and the successor coordinates are 0,3,1,2,3. These outcome codes are distinct. Writing f and s for these two tables, direct expansion gives I_f(i)(X) = X_ii P_s(i), with P_o the coordinate projection, for every complex matrix X; the unused branches 1,2,4 are zero. In particular, Tr(I_7(X)) = X_44 without a diagonal-input restriction. Summing the branches gives diag(X_00,X_22,X_33,X_11 + X_44). Thus this chosen channel discards all off-diagonal source entries.

On a density input X, the complete classical record distinguishes the two rejected sources: source index 1 has outcome 3 and source index 4 has outcome 7, although both have successor coordinate 3. Keeping only the reply merges their recorded masses into X_11 + X_44; the resolved odd-rejection branch instead retains X_44. This distinction uses the fixed K family and the stated record permissions. It does not specify a physical preparation or an implementation of the required record operations.

The same stipulated family has an exact finite-reference action. For any finite reference index R and every complex matrix Z on the product of the source and R, the (o,r),(o',r') entry of (I_b tensor id_R)(Z) is the sum of Z_(i,r),(i,r') over i satisfying b = f(i) and o = o' = s(i). Thus cross-source blocks are discarded, while the reference block at a fixed source is retained in that branch. This is a matrix identity for the specified lifting, with no claim of an available native reference carrier or coherent control.

A full basis-poststate contract gives a further conditional application. Let Phi_b be arbitrary completely positive complex-linear maps from the five-source matrices to the four-output matrices, and require Phi_b(E_ii) = P_s(i) when b = f(i), and zero otherwise, for every b and i. These are complete branch poststates, not just outcome probabilities. The actual distinct outcome codes then force Phi_b(X) = sum_i [b = f(i)] X_ii P_s(i) for every complex X. The positive-Choi and reconstruction lemmas in `D5/S3/Quantum/Foundation/FiniteKrausRepresentation` give the derivation: every inactive source has a zero diagonal Choi block; positive semidefiniteness annihilates its columns and rows. Injectivity leaves at most one active source in each branch, so every off-diagonal input block vanishes, and Choi reconstruction gives the displayed action. This fixes the CP branch maps under that contract, without fixing a Kraus decomposition or coherent dilation. A probabilities-only contract leaves output states free. This ordinary application reuses existing results and adds no Lean declaration; it does not establish a physical preparation, native implementation, LOCC protocol or success-rate bound.

The generic diagonal Kraus theorem supplies completeness, nonnegative weights, the channel obtained by summing branches, and the factorization criterion. This FIB application consumes those results at one actual continuation and stops there: it does not add a generic quantum wrapper, put provenance in the density matrix, or transport the result to arbitrary acquired tree histories.

Dependencies: the existing ImmediateWindowStateCapacity reader and the JointLaw native continuation semantics, together with the frozen diagonal Kraus factorization.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.branch_trace_is_hidden_joint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.diagonal_readout_consumer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.native_reply_table`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw](../JointLaw.md)
- Dependency: [D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization](../../../../Quantum/Measurement/DiagonalKrausInstrumentFactorization.md)
- Narrative reference: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../../../Quantum/Foundation/FiniteKrausRepresentation.md)
