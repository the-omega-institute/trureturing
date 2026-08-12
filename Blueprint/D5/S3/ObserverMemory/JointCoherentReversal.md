# Joint Reversal of Unimodular Record Phases

## Abstract

Amplitude conjugation reverses unimodular record-overlap phases under composed finite-record channels.

**Theorem 1.1 (Reversing all unimodular record phases restores the selected entry).**

$$\forall R, \rho, i, j,\ (\forall k,\ \overline{g_{k}(i, j)} g_{k}(i, j)=1) \Rightarrow\\\operatorname{channel}(\operatorname{reverse}(all, R), \operatorname{channel}(R, \rho))_{ij}=\rho_{ij}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/JointCoherentReversal.joint_coherent_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family of record factors act through the imported product channel. The record operation reverseRecord conjugates every complex amplitude of the selected existing record; reverse_record_overlap proves that this conjugates its Gram overlap. If conjugate(g_k) times g_k is one for every copy at the selected addresses, the reversed-family channel is applied to the output of the original-family channel and the two overlap products cancel.

This proves entrywise recovery only for the displayed unimodular-overlap family inside the deposited record-vector model. That frozen model does not expose record-generating unitaries, so the theorem does not construct an inverse unitary interaction or provide a recovery guarantee outside the stated overlap hypothesis. It makes no claim about inverting an arbitrary traced physical channel.

The proof reuses the frozen finite-copy channel equation. Local library searches checked map_sum, map_mul, Finset.prod_mul_distrib, Finset.prod_ite, and Complex.I_mul_I. The imported structure exposes no record-generating unitary inverse.

**Theorem 1.2 (One surviving phase copy blocks restoration).**

$$(\forall l,\ l\neq k \Rightarrow \overline{g_{l}(i, j)} g_{l}(i, j)=1) \land g_{k}(i, j)\neq1 \land \rho_{ij}\neq0 \Rightarrow\\\operatorname{channel}(\operatorname{reverse}(all\setminus\{k\}, R), \operatorname{channel}(R, \rho))_{ij}\neq\rho_{ij}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/JointCoherentReversal.surviving_copy_blocks_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse every copy except k and assume the other overlaps obey the same unimodularity law. The composed channel then multiplies the original entry by the surviving overlap g_k. If that overlap is not one and the input entry is nonzero, the result differs from the input. This is an entrywise obstruction for one surviving record factor, not a general no-recoherence theorem.

**Theorem 1.3 (Two copies separate partial from joint reversal).**

$$\rho_{01}=\frac{1}{2} \land\\\operatorname{channel}(R_{two}, \rho)_{01}=-\frac{1}{2} \land\\\operatorname{channel}(\operatorname{reverse}(\{0\}, R_{two}), \operatorname{channel}(R_{two}, \rho))_{01}=-i\frac{1}{2} \land\\\operatorname{channel}(\operatorname{reverse}(all, R_{two}), \operatorname{channel}(R_{two}, \rho))_{01}=\frac{1}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/JointCoherentReversal.two_copy_joint_reversal_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take two identical phase records whose zero-one overlap is minus i and the normalized equal-superposition density matrix. The original two-record channel changes its one-half entry to minus one-half. Applying only the copy-zero conjugate channel gives minus i over two, while applying the fully conjugated family channel to that same channel output restores one-half. This witnesses reversible phase cancellation, not recovery of zero-overlap decoherence.

## References

- Truth anchor: `D5/S3/ObserverMemory/JointCoherentReversal.joint_coherent_reversal`
- Truth anchor: `D5/S3/ObserverMemory/JointCoherentReversal.surviving_copy_blocks_reversal`
- Truth anchor: `D5/S3/ObserverMemory/JointCoherentReversal.two_copy_joint_reversal_certificate`
- Dependency: [D5/S3/ObserverMemory/MultiCopyErasure](MultiCopyErasure.md)
