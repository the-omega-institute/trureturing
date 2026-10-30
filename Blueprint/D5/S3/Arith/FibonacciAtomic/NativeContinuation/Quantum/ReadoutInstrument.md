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

The same-K comparison fixes three distinct carriers. Put K_b = K () b (), Phi(X) = sum_b K_b X K_b*, and Psi(X) = sum_b (K_b X K_b*) tensor |b><b|. Here the output-first product coordinates are (o,b) in Fin 4 times Fin 8; Psi retains the complete classical outcome, including parity. To use the C-Q supplier on Fin 32, swap to (b,o) and flatten by 4b+o. The five output states are sigma_i = P_s(i) for Phi (n=5,d=4), and tau_i = P_(4f(i)+s(i)) for the reindexed Psi (n=5,d=32). The latter coordinates are (0,15,21,26,31). Every state is positive semidefinite with trace one. For every complex input X, both maps depend only on X_ii: their outputs are sum_i X_ii sigma_i and sum_i X_ii tau_i. Consequently their action on |u><u| is exactly channelOutput with coefficients |u_i| squared.

For 2 <= k <= 5, use the supplier's orthonormality condition sum_i conjugate(u_r(i)) u_t(i) = delta_rt and its averageOutputOverlap: sum over ordered unequal pairs (r,t), divided by k(k-1), of the real trace of the product of their output states. The sharp minima over all such unit-vector families, in order k=2,3,4,5, are (0,0,0,1/10) for Phi and (0,0,0,0) for Psi. Indeed Tr(sigma_i sigma_j) = [s(i)=s(j)] and Tr(tau_i tau_j) = [i=j]. The only distinct-source collision is {1,4}. Prefixes of the common source order (0,2,3,1,4) give orthonormal source basis families attaining both minima. Up to size four their outputs are distinct; size five has exactly two ordered colliding pairs for Phi, giving 2/20, and none for Psi.

The basis computation alone is not a bound on arbitrary orthonormal families. The missing quantifier is supplied by `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap` result, applied separately to these two density-state families. Its minDistinctOverlap is the infimum over injective Fin k to Fin 5 maps. Every basis score is nonnegative; for k=5 each injection is a permutation and the Phi score is 1/10. The displayed common families attain these bounds, so the supplier proves exactly the claimed minima for all orthonormal inputs. Hutton, Mehta and Vukovic, arXiv:2508.10664v1, Definition 1.3 and Conjecture 1.5 (pp. 2-3), supply the C-Q setting and question; the proved general-k lower bound here is the repository result, not a theorem attributed to that paper. This is a finite application of that result, not a new general overlap theorem.

Fixing these actual Kraus matrices also selects one coherent lift: V|i> = |s(i)> tensor |f(i)>, with V_(o,b),i = (K_b)_o,i and V*V = I_5. Write L(X)=VXV*. For every complex X its (o,b),(p,c) entry is sum_(i,j) [o=s(i), b=f(i), p=s(j), c=f(j)] X_ij. Tracing the record gives Phi(X); dephasing the record basis gives Psi(X). Tracing the output instead gives the fixed complementary channel Gamma(X), with Gamma(X)_(f(i),f(j)) = [s(i)=s(j)] X_ij and zero unused rows/columns. Its only off-diagonal block is on environment coordinates (3,7), where the block is [[X_11,X_14],[X_41,X_44]]. The other active entries are Gamma_00=X_00, Gamma_55=X_22, Gamma_66=X_33. Thus, on its active support, the retained environment has the concrete block algebra C^3 direct-sum M_2; it discards coherences between different s-fibers.

This is one same-K realization of the standard Kraus/Stinespring correspondence, with the complete representation locators in Library/Quantum/watrous2018theory.md (Theorem 2.22, Theorem 2.26 and Corollary 2.27). The environment-record mechanism already appears in `D5/S3/Quantum/EnvironmentRecords`; the branch-versus-cross-block distinction is also stated in AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION, Proposition 6.5. Branch maps alone do not choose this lift or its relative record phases. With access to the intact joint image, V*L(X)V=X for every X. This is information preservation on the stipulated joint carrier, with an algebraic left inverse on that image; it does not supply a native inverse operation or physical control.

The complement of the already recorded Psi is different. A dilation is W|i> = |s(i),f(i)>_(output,record) tensor |f(i)>_E'. Its system marginal is Psi and its complementary output is sum_i X_ii |f(i)><f(i)|, which is diagonal because f is injective. Equivalently, copying the record of V into E' and discarding E' dephases that record. After this step, tracing the output of Psi gives the diagonal of Gamma, not Gamma itself. The copied classical record and an undisturbed collision-phase block are therefore not supplied simultaneously. W still preserves information on its full coherent joint image if every factor is actually retained; losing that carrier changes the available predictions.

For a concrete phase test take source rays z_+ = (e_1 + i e_4)/sqrt(2) and z_- = (e_1 - i e_4)/sqrt(2), with density matrices rho_+ and rho_-. Both give Phi(rho)=P_3 and Psi(rho)=(P_(3,3)+P_(3,7))/2. Gamma instead gives the orthogonal projectors onto (e_3 + i e_7)/sqrt(2) and (e_3 - i e_7)/sqrt(2). The non-diagonal environment effect onto the plus ray has probabilities one and zero. Its implementation requires coherent preparation, access to the unmeasured environment, and a calibrated phase reference for that effect. It is not classical feedback. Since Phi and Psi identify these two distinct inputs, no map using only either of those outputs can recover every unknown input state.

The existing `D5/S3/Quantum/Fibers/FiveModePhaseLift` certificate uses source coordinates (2,4), whose successors are 1 and 3. That coherence survives in the joint L entries connecting (1,5) and (3,7), but both marginal traces kill it; Gamma alone cannot recover that certificate. The collision test above uses (1,4) precisely because both successors are 3. These are two different phase locations, not interchangeable witnesses.

For the quantum-origin question, this application identifies which predictions are merged by a chosen readout and where a stipulated coherent realization carries the missing distinctions. It does not derive the complex-state model or Born probabilities from the native reader. A common native realization of coherent preparation and joint dynamics, phase-referenced noncommuting effects and their legal controls, an operation-preserving source map to full FIB histories, and a physical probability/Born bridge remain unsupplied. Fin 5 labels only the five initialized windows above; it is neither the full infinite FIB source nor NativeContinuation.Source(3).

The generic diagonal Kraus theorem supplies completeness, nonnegative weights, the channel obtained by summing branches, and the factorization criterion. This FIB application consumes those results at one actual continuation and stops there: it does not add a generic quantum wrapper, put provenance in the density matrix, or transport the result to arbitrary acquired tree histories.

Dependencies: the existing ImmediateWindowStateCapacity reader and the JointLaw native continuation semantics, together with the frozen diagonal Kraus factorization.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.branch_trace_is_hidden_joint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.diagonal_readout_consumer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/ReadoutInstrument.native_reply_table`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw](../JointLaw.md)
- Dependency: [D5/S3/Quantum/Measurement/DiagonalKrausInstrumentFactorization](../../../../Quantum/Measurement/DiagonalKrausInstrumentFactorization.md)
- Narrative reference: [D5/S3/Quantum/EnvironmentRecords](../../../../Quantum/EnvironmentRecords.md)
- Narrative reference: [D5/S3/Quantum/Fibers/FiveModePhaseLift](../../../../Quantum/Fibers/FiveModePhaseLift.md)
- Narrative reference: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../../../Quantum/Foundation/FiniteKrausRepresentation.md)
- Narrative reference: [D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap](../../../../Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.md)
