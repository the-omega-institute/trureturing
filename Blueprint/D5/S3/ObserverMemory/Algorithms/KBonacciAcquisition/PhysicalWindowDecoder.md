# Donor rows, both physical branches and exact final decoding

## Abstract

One physical suffix and final-only original INITIAL decoder.

**Definition 1.1 (One code coordinate at each ordered vertex).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.vertexBit`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.vertexBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A selected label code supplies a scalar bit at each ordered child vertex. Repeated occurrences of one label retain their separate vertices.

**Definition 1.2 (The donor-compensated actual charge).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.physicalCharge`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.physicalCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On each of the m+1 child vertices the charge is its selected code coordinate. At the absent donor m+1 it is the sum over all child vertices, counting every repetition. The selected unavailable vertex contributes zero.

**Definition 1.3 (Rows at their actual issued indices).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualRow`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate i rotates the physical charge to the complete window beginning at (i+1)m modulo m+2. Offsets zero through m are the full ordered window.

**Definition 1.4 (All code coordinates in order).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualRows`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is exactly one ordered charge row for each of the d code coordinates.

**Theorem 1.5 (Parity and the direct literal inverse).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.donor_rows_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.donor_rows_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least three, every repeated-label table, fitting coordinate dimension, selected unary zeros and each coordinate, the unavailable offset m+1 is zero and the complete row has even charge. The native short-window inverse directly realizes this row. Its first and last literal bits are zero exactly when the corresponding endpoint charges are zero.

**Theorem 1.6 (The regular Selection supplies every seam zero).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.regular_rows_safe`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.regular_rows_safe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three and d at least two, the regular selected code lists force the first row head zero and safeRows for all ordered rows. Each later common boundary has zero in at least one adjacent literal bit. No additional safety hypothesis is assumed.

**Theorem 1.7 (The actual issued-phase code).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.issued_phase_code`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.issued_phase_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prior archive length a, child vertex v and coordinate i, the literal row at actual issued index a+i+1 increments the native scalar by that vertex label code coordinate. The modular phase includes the complete prior archive rotation.

**Theorem 1.8 (The exact four-label charges).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.exceptional_row_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.exceptional_row_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit four-label code assignment at dimension two makes the first head charge zero, its last and preceding charges one, and the second first three charges 1,0,1. This holds for every m at least three, including m=3, with arbitrary repeated occurrences elsewhere in the table.

**Theorem 1.9 (The exceptional two-word seam).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.exceptional_literal_execution`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.exceptional_literal_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every incoming scalar, phase and valid tail, the exact selected first word starts zero and ends 01, with terminal tail exactly one. The second word begins 110. Its crossing run is three, strictly below k=m+1 including m=3. The first native step succeeds and the second succeeds by first_zero_block_exact, without safeRows or a repair word.

**Definition 1.10 (The actual fixed-script archive).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.scriptArchive`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.scriptArchive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recursively issue every complete word and pair it with that source record's own endpoint. The script does not stop early, including on rejection.

**Definition 1.11 (The forced-final archive-only selector).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.finalSelector`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.finalSelector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selector indexes the prescribed words by its own archive length after the acquired prefix. It issues every available prescribed word before calling the decoder on its own suffix archive. It reads no source phase, hidden clock or sibling reply.

**Theorem 1.12 (The original selector pays the exact script length).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.original_final_script`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.original_final_script` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary label type, k at least two, block width, fixed complete-word list, decoder, given original history, free reading and acquired prefix, the prescribed selector has a PaidTrace issuing exactly that list. The issued archive length and returned original fee both equal the full script length; the decoder is called only after every word. Rejecting words are still paid. This theorem alone does not assert decoder correctness or successful endpoints.

**Definition 1.13 (The fixed physical suffix).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualWords`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map every selected ordered donor row through the native prefix-parity inverse, in code coordinate order. Each complete word has width m and is legal in both original alphabets because m is less than k.

**Definition 1.14 (Only own-endpoint differences).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.endpointDifferences`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.endpointDifferences` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the remembered scalar from the next actual endpoint and continue from that endpoint. Rejection is retained as an unavailable difference; no source coordinate is read.

**Theorem 1.15 (Both branches give all code coordinates).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.physical_endpoint_codes`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.physical_endpoint_codes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary odd m at least three, fitting d at least two, repeated-label table and actual Selection, each child vertex starting at the common value and inherited tail one executes the same d literal words. Every endpoint succeeds, and its own successive differences equal all that vertex label code coordinates. The regular branch uses safeRows implied by Selection; the exceptional branch uses the exact terminal01 and prefix110 proof. Both alphabets remain universal. Each supplied native starting record determines its own actual endpoint sequence.

**Definition 1.16 (The full final code vector).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.codeVector`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.codeVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected binary code is represented as d successful endpoint differences in their original coordinate order.

**Definition 1.17 (Decode only the final own archive).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.decodeArchive`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.decodeArchive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Match the final own-endpoint differences to the fixed selected code table and return the matching label. A fallback exists only for transcripts outside the stated compatible source fiber.

**Theorem 1.18 (One complete original-source physical INITIAL decoder).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.original_physical_initial_decoder`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.original_physical_initial_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd m at least three and k=m+1, fix either original alphabet, an arbitrary acquired archive with remembered free scalar and prior endpoint, a successful positive parent, full surviving phase support equal to its physical window, and the assumed per-phase factorization of immutable INITIAL labels. If the actual rotated table has at least three distinct labels, let d be its binary ceiling logarithm. There exist injective selected codes and one archive-only original selector issuing the same complete donor-compensated suffix on every given original history compatible with that same entire archive. Every issued endpoint succeeds; the actual issued words equal the displayed suffix and their number is exactly d. The final own-endpoint differences equal the entire selected code of a label explicitly equal to f(INITIAL). The prescribed selector has a same-record PaidTrace and returns the immutable f(INITIAL) in the original execute with exact additional fee d. Every emitted word is legal; no early stop, omitted paid word, wait, reset, repair, hidden observation or sibling information is used. The proof derives each history's actual current phase, scalar and tail one from OriginalAcquiredTrace; arbitrary repeated labels remain in scope. This is suffix attainment, not a minimum-price or GLOBAL theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualRow`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualRows`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.actualWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.codeVector`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.decodeArchive`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.donor_rows_inverse`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.endpointDifferences`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.exceptional_literal_execution`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.exceptional_row_coordinates`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.finalSelector`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.issued_phase_code`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.original_final_script`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.original_physical_initial_decoder`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.physicalCharge`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.physical_endpoint_codes`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.regular_rows_safe`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.scriptArchive`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder.vertexBit`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace](OriginalAcquiredTrace.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes](WindowSeamCodes.md)
