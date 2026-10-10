# The original acquired-history and paid-trace foundation

## Abstract

Actual acquired histories retain immutable INITIAL records and exact paid traces.

**Definition 1.1 (Absolute issued-block vertices).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.vertex`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex at offset i of complete block a is am+i modulo k+1. The issued index counts every block, including waits and zero words.

**Definition 1.2 (The ordered complete window).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.physicalWindow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.physicalWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support window includes all m+1 vertices from offset zero through m in their original modular order.

**Definition 1.3 (The complete emitted prefix).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archiveWords`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archiveWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Flattening the archive retains every position of every complete word in chronological order. Endpoint replies contribute no extra bits.

**Definition 1.4 (One history and its own chronological endpoints).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.ActualArchive`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.ActualArchive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each archived reply is the original output after that history and every preceding complete archived word. Rejection remains part of the same absorbing original execution.

**Definition 1.5 (INITIAL and current records of the same source).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.AcquiredPairs`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.AcquiredPairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fiber quantifies all allowed original source histories compatible with the one remembered free output and the entire acquired archive. Each pair retains its original INITIAL record and its current record after exactly those archived words. Both original alphabets remain parameters.

**Definition 1.6 (A stopped chronological paid trace).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.PaidTrace`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.PaidTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A leaf emits no more words. Each action is selected from the source's own prior archive, and its reply is the actual endpoint of that action on the current original record.

**Definition 1.7 (The remembered last endpoint).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archiveEndpoint`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archiveEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An empty archive retains the free output. A nonempty archive retains its last chronological reply.

**Definition 1.8 (All surviving INITIAL phases).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.initialSupport`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.initialSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A phase belongs to the support exactly when a compatible original history retains that INITIAL phase in the common acquired archive.

**Theorem 1.9 (Splitting a common archive).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_archive_append`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_archive_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Archive concatenation preserves the entire emitted prefix and starts the second archive from that same extended original history.

**Theorem 1.10 (The actual reply fiber).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_archive_reply`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_archive_reply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending a complete word and its actual reply gives exactly the corresponding native reply fiber. The INITIAL coordinate is unchanged, including on later rejection.

**Theorem 1.11 (Exact stopped fees).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.native_execute_paid_trace`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.native_execute_paid_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Native execution returns a label and fee c exactly when a stopped paid trace with c complete words exists within the supplied horizon d. The horizon is an upper bound and need not equal the actual fee. Zero-budget stops and rejecting actions are included.

**Theorem 1.12 (Original execution has the same exact trace).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.execute_paid_trace`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.execute_paid_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original integer-weight scanner execution and the native record execution return the same label and exact stopped fee. Every reply belongs to the same source history; this equivalence introduces no extra observation.

**Theorem 1.13 (Current coordinates of an actual positive child).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_positive_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_positive_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least three and m less than k, every compatible source in the successful positive child has current scalar previous+1, valid actual tail, and phase INITIAL phase+(a+1)m, where a is the preceding archive length. Its parent charge is one at its retained INITIAL phase, and its support is contained in the physical window. Positivity alone does not imply full support or tail one.

**Theorem 1.14 (Exact fees preserve the original fiber).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.acquired_execution_trace`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.acquired_execution_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original allowed history matched to the acquired archive, returning f of its INITIAL record at fee c is equivalent to a chronological stopped trace of length c within horizon d. The combined archive consists of that source's own endpoints and retains the original INITIAL coordinate in the final acquired fiber. No controller or suffix is supplied by this equivalence.

**Theorem 1.15 (The full positive parent and inherited tail).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.full_positive_parent`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.full_positive_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd m at least three, m less than k, and full surviving phase support equal to the parent window, the actual parent is the alternating word beginning and ending in one. Its internal zero clears all surviving incoming tails and its terminal tail is exactly one. The proof uses the unique native prefix-parity inverse of the constant-one even charge row.

**Theorem 1.16 (The labelled full-positive history foundation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.full_positive_history_trace`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.full_positive_history_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd m at least three and k=m+1, one shared original positive archive with full phase support has the actual alternating parent. Every compatible source retains its INITIAL record, label, all current state coordinates, and its own original chronological execution with exact stopped fee. The current scalar is previous+1, the tail is one, and the current phase is INITIAL phase+(a+1)m, where a is the preceding archive length. Every original allowed history compatible with the fixed free scalar and the entire acquired archive is quantified. For every selector, horizon d, and returned fee c, returning f(INITIAL) is equivalent to a stopped own-endpoint trace of length c with c at most d; its combined archive and final record come from this same given history. The per-phase INITIAL label law is an explicit substantive hypothesis; legality does not imply it. The source history is retained rather than replaced by a newly realized pointwise record.

The selected physical suffix and its decoder also require donor-compensated rows, separate safety proofs for both seam alternatives, endpoint-code correspondence, and a stop after exactly d blocks. These properties are distinct from the trace equivalence. No optimal price, adaptive lower bound, constant or binary price, or GLOBAL policy follows from this equivalence.

**Theorem 1.17 (Every issued archive entry contains one complete m-bit word).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archive_length`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archive_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and chronological archive, the length of archiveWords is exactly archive.length times m. The flattening includes all bits of every issued complete word, even zeros, clearing, waits and the remainder of a word rejected internally. Combining this identity with a stopped PaidTrace transfers the exact block fee to the emitted-bit fee.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.AcquiredPairs`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.ActualArchive`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.PaidTrace`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.acquired_execution_trace`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_archive_append`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_archive_reply`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.actual_positive_coordinates`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archiveEndpoint`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archiveWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.archive_length`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.execute_paid_trace`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.full_positive_history_trace`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.full_positive_parent`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.initialSupport`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.native_execute_paid_trace`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.physicalWindow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace.vertex`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse](WindowChargeInverse.md)
