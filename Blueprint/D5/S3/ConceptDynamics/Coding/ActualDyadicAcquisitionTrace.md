# Actual Continuation Capacity and Saturation

## Abstract

Actual saturated dyadic sensor continuations force chronological midpoint reads and pair-local final queries.

**Theorem 1.1 (Capacity saturation excludes early stopping).**

$$\begin{gathered}Success \implies CandidateCard \leq \operatorname{pow}(2, remaining)\\{}\operatorname{eq}(CandidateCard, \operatorname{pow}(2, remaining)) \implies \operatorname{ReadSaturation}(remaining)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_continuation_capacity_and_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive block length, a known initial binary high bit, and a deterministic policy on the complete event and raw-read record. The only actions are one forward event, a nondisturbing literal sensor read, and a successful stop. Successful finite executions may stop before making another read; a cutoff is not a successful execution.

Suppose every source in a finite candidate set has an actual successful continuation from the same complete record, using at most d new reads and returning that source. The candidate set has at most 2^d elements. Its histories and event counts need not range over finite domains.

Encode each continuation by its raw bits and mathematical zero padding. Two executions with equal codes replay the same deterministic advances, reads and stopping decision. Induction over the actual finite execution therefore gives the same terminal record and output. Exact outputs make the encoding injective; finite function cardinality gives the bound.

If the candidate set attains 2^d elements, the finite encoding is onto. An alleged shorter successful continuation can be extended by a code whose first padded position is one. Its actual realization shares the old raw prefix and must stop with the same word, contradicting zero padding. Every such continuation using at most d new reads has exactly d reads.

This capacity bound does not assert dyadic interval rigidity, a final query phase, a causal noisy-phase decoder, or repair label thresholds.

**Theorem 1.2 (Silent forward evolution reaches a common next-read event).**

$$NonemptyActualRun \implies SharedNextRead$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_next_read_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix one complete record and one successful actual execution with at least one new read. There is a finite event count N at least as large as the current count. The policy advances at every intervening event with the old read record and chooses a read at N.

Every other successful execution with a new read from the same complete record reaches that same N. Its first bit is the literal sensor at N, and its tail is an actual execution from the record with that bit appended. The proof extracts the finite silent segment from the first execution and uses the conflicting advance and read choices to exclude different first-read events.

Nonempty actual words are a hypothesis here; capacity saturation supplies them for a positive full read budget. This result does not assume that an arbitrary cutoff or empty execution has a last read.

**Theorem 1.3 (Actual dyadic continuations force the chronological midpoint trace).**

$$SaturatedIntervalSuccess \implies ForcedReadTrace$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_dyadic_interval_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a common complete record and the original source interval [a,a+2^d), contained in a positive block. Every source in that interval has an actual identifying continuation with at most d new physical reads. For each such actual continuation, its final read record is the old record followed by a forced chronological trace.

At a node with d+1 remaining reads, extract the common next actual query N. The literal raw sensor partitions the interval at theta=P-(N mod P). Its two actual children have at most 2^d sources by remaining-read capacity. Natural interval cardinality therefore forces theta=a+2^d. Both children admit actual successful continuations from their corresponding appended raw records.

Induction on the remaining budget applies the same construction in the child selected by the acquired threshold bit. Every recorded query has the forced midpoint phase and its raw value is (b+floor(N/P)+e) mod 2. The full event quotient preserves arbitrary whole-period waits. Query counts remain nondecreasing in the model.

The trace contains actual read event counts; subsequent silent reporting advances do not change it. The common pair-local final query is established by the following actual two-run theorem.

**Theorem 1.4 (The actual source pair shares its pre-final record and last query).**

$$ActualPairedExecutions \implies CommonPrefinalRecordAndQuery$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_pair_common_final_query` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consider two actual executions from the same complete record, with source representatives having the same quotient by two. Both sources are in one dyadic interval with even lower endpoint, have the saturated positive read count, and have the forced chronological traces supplied by the interval theorem. The traces agree before their last entries, whose literal event count N is also common.

At every earlier midpoint, its even threshold puts the paired sources on the same side. Their raw bits therefore agree. The common-next-read decomposition moves both actual continuations to the same appended complete record. Induction reaches the final two-source interval, where the next physical query is the last read for both executions.

For t=floor(r/2), the actual event obeys N mod P=P-1-2t. The two literal final bits are (b+floor(N/P)+(r mod 2)) mod 2 and the analogous expression for the other source. The policy chooses read on the common pre-final record. From each appended final-bit record an actual execution with no further reads reaches its original terminal record.

The event quotient retains every whole-period wait, and the common N is local to the source pair. These operational results do not supply a chronological prefix writer, an all-error noisy-phase decoder, or the TM8.1 label and supplementary-bit thresholds.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_continuation_capacity_and_saturation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_dyadic_interval_trace`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_next_read_decomposition`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ActualDyadicAcquisitionTrace.actual_pair_common_final_query`
