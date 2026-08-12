# Record-Environment Partial Bridge

## Abstract

A one-entry record channel is an environment marginal, while homogeneous finite record-channel composition is iterated phase damping under the same Gram rule.

**Theorem 1.1 (A one-entry record channel is the environment marginal).**

$$\forall R, c, \rho,\  \forall i, j,\  g_{R}(i, j)= if i=j then 1 else c \Rightarrow \\\operatorname{tr}_{E}(J_{R}(\rho))= \operatorname{multiRecordChannel}_{Unit}(R, \rho).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/LedgerEnvironmentBridge.one_record_channel_is_environment_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any frozen environment record whose Gram overlaps have phase-damping coefficient c, tracing the frozen controlled joint state is equal to the frozen finite-record channel indexed by the one-element type. Both sides exist independently of this bridge. The frozen EventHistory API exposes no map from the ledger opcode to an environment record, so no such semantics is postulated here.

**Theorem 1.2 (Finite record-channel composition is iterated decoherence).**

$$\forall R, c, N, \rho,\  \forall i, j,\  g_{R}(i, j)= if i=j then 1 else c \Rightarrow \\\operatorname{multiRecordChannel}_{Fin N}(R, \rho)= \operatorname{phaseDampingIterate}(c, N, \rho).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/LedgerEnvironmentBridge.finite_record_channel_is_iterated_decoherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N copies of the same normalized frozen record, the existing finite-family record channel equals N iterations of the existing phase-damping map. The common Gram-overlap premise determines the retained off-diagonal factor, so the statement identifies two independently frozen constructions rather than unfolding a newly defined history channel. This is the strongest frozen bridge; it does not identify EventHistory bookkeeping with quantum evolution.

**Theorem 1.3 (Two copied-address records erase both coherences).**

$$rho:= \rho_{+}, rhoB:= \operatorname{multiRecordChannel}_{Fin 2}(copy, rho), rhoD:= \operatorname{phaseDampingIterate}(0, 2, rho),\\\operatorname{tr}_{E}(J_{copy}(rho))= \operatorname{multiRecordChannel}_{Unit}(copy, rho) \land rhoB=rhoD \land \\rhoB_{00}=\frac{1}{2} \land rhoB_{11}=\frac{1}{2} \land rhoB_{01}=0 \land rhoB_{10}=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/LedgerEnvironmentBridge.record_decoherence_anti_vacuity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the same equal-superposition density matrix, the one-record environment marginal agrees with the one-entry finite record channel. For two copied-address records, finite record-channel composition agrees with two zero-retention damping steps, preserving both one-half populations and sending both coherences to zero.

## References

- Truth anchor: `D5/S3/ObserverMemory/LedgerEnvironmentBridge.finite_record_channel_is_iterated_decoherence`
- Truth anchor: `D5/S3/ObserverMemory/LedgerEnvironmentBridge.one_record_channel_is_environment_marginal`
- Truth anchor: `D5/S3/ObserverMemory/LedgerEnvironmentBridge.record_decoherence_anti_vacuity`
- Dependency: [D5/S3/ObserverMemory/MultiCopyErasure](MultiCopyErasure.md)
