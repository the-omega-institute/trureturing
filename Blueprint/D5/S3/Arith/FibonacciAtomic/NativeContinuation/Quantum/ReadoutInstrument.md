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

For the reply-only record, define J_b = I_b + I_(b+4) for b = 0,1,2,3. There is a conditional uniqueness statement for these coarse branches even though replyCode is not injective. In the source order (0,2,3,5,25), write q = replyCode and s = successorCode; both tables are (0,3,1,2,3). Let Phi_b be arbitrary complex-linear completely positive maps from complex 5-by-5 matrices to complex 4-by-4 matrices. Require total trace preservation sum_b Tr(Phi_b(X)) = Tr(X) for every complex matrix X, and require the full unnormalized poststates Phi_b(E_ii) = [b = q(i)] P_s(i) for every b and i, where E_ij is the source matrix unit and P_o is the output coordinate projection. Then Phi_b(X) = J_b(X) = sum_i [b = q(i)] X_ii P_s(i) on every complex input. In particular Phi_3(X) = (X_11 + X_44) P_3, and summing the coarse branches gives the same total diagonal channel displayed above.

The coarse derivation uses the positive Choi matrix of each Phi_b. A zero diagonal entry annihilates the corresponding column and row by Matrix.PosSemidef.dotProduct_mulVec_zero_iff. The poststate table therefore annihilates inactive source blocks and all output coordinates other than b, using s = q. For i distinct from j, every branch except q(i) vanishes on E_ij. Applying total trace preservation to E_ij forces the trace of the remaining branch to zero. Its only possible output entry is (q(i),q(i)), so that whole output vanishes too. This step includes the two distinct rejected sources i = 1 and j = 4; it uses trace preservation on off-diagonal matrix units. Choi reconstruction then gives the stated action, and expanding the existing K family identifies it with J_b.

The mature pure-state correspondence is Chefles, Jozsa and Winter, arXiv:quant-ph/0307227v1 (https://arxiv.org/pdf/quant-ph/0307227v1), Theorem 2 on page 4, Corollary 2 on page 5, and Theorem 3 on page 6, equations (7)-(8). For Theorem 3 take the five orthonormal source kets, branch probabilities P_i^b = [b = q(i)], and target ket |b> in branch b for every i, including its zero-probability entries. Embed the four output coordinates isometrically into the five-dimensional source space to match the theorem's common finite Hilbert space. The source Gram matrix is I_5 and each branch target Gram matrix is the all-ones matrix. Their condition is therefore I_5 = sum_b Pi^b, with Pi^b positive semidefinite and diagonal [b = q(i)]. Zero-diagonal rows vanish; each off-diagonal pair can remain in at most one branch, where the sum condition makes it zero. Hence Pi^b = diag_i [b = q(i)]. This is the Gram correspondence for the same finite application, with total branch probability one and no omitted failure probability.

Corollary 2 applies on each fixed source fiber q(i) = b after restriction: the other branches vanish there, the restricted branch is trace preserving, and all its targets are the identical P_b, with pairwise overlap one. Theorem 2 then has source Gram I and target Gram all ones on that fiber. Corollary 2 does not apply directly to the entire four-output target family, whose different output coordinates are orthogonal. Rank-one-effect instrument criteria also do not apply directly to the rejection effect E_11 + E_44, which has rank two. This is an application of mature results; the direct matrix derivation uses the existing Choi and kernel suppliers.

The coarse uniqueness conclusion requires both the branch weights and their complete poststates. Outcome probabilities without output states, or normalized pure outputs without their weights, specify weaker data; mixed target poststates are outside this argument. The conclusion fixes the finite branch maps under the stated contract. It does not recover the original parity or kappa from a merged output, choose a Kraus decomposition or dilation, or supply a native or physical implementation, LOCC protocol, yield bound or quantum field theory.

The generic diagonal Kraus theorem supplies completeness, nonnegative weights, the channel obtained by summing branches, and the factorization criterion. This FIB application consumes those results at one actual continuation and stops there: it does not add a generic quantum wrapper, put provenance in the density matrix, or transport the result to arbitrary acquired tree histories.

Dependencies: the existing ImmediateWindowStateCapacity reader and the JointLaw native continuation semantics, together with the frozen diagonal Kraus factorization.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.branch_trace_is_hidden_joint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.diagonal_readout_consumer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.native_reply_table`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw](../JointLaw.md)
- Dependency: [D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization](../../../../Quantum/Measurement/DiagonalKrausInstrumentFactorization.md)
- Narrative reference: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../../../Quantum/Foundation/FiniteKrausRepresentation.md)
