# PaddedCompletion

## Abstract

Padded certificates and concatenation in the exact Mertens range-two proof.

**Definition 1.1 (oldIndex).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldIndex`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Embed both old pieces in the padded interval, preserving the six-site separation.

**Definition 1.2 (bufferIndex).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.bufferIndex`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.bufferIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Embed the six buffer sites between the old pieces.

**Definition 1.3 (paddedOffset).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedOffset`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The whole interval displacement preserves each old assignment, including singles and exterior requests, and uses the actual request completion at the six inserted vertices.

**Theorem 1.4 (padded_certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of certified words the concrete padded word has a full certificate. Occupied buffer vertices reverse actual old requests; free vertices use the involutive layout. Reciprocity gives injectivity at every internal target, and unchanged old targets give injectivity at exterior targets. Old edges preserve their original tests. Each other edge has a matched buffer endpoint whose assigned partner is first, because a central buffer single has only matched buffer neighbors. No parity or perfect-matching assumption is used.

**Definition 1.5 (paddedCertified).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedCertified`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedCertified` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Return the original padded ranking word as a certified word, using its proved concrete displacement certificate.

**Theorem 1.6 (count_padded_supermultiplicative).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.count_padded_supermultiplicative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.count_padded_supermultiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the two certified profile counts is at most the count at length m+k+6, for all natural lengths and hence every m,k at least one. The injection recovers the two ranking words; neither certificate choices nor matching witnesses are counted. GrowthTransfer.result consumes this inequality together with CyclicClosure and TriangleCount in the same-base probability estimate.

**Definition 1.7 (partnerFirst).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.partnerFirst`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.partnerFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The deterministic strict permutation places any prescribed nonzero offset first.

**Definition 1.8 (chosenOffset).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.chosenOffset`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.chosenOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose one certificate per preference word. The choice is used in the construction and is not counted as an additional outcome.

**Definition 1.9 (paddedBuffer).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedBuffer`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedBuffer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual six buffer rankings put each assigned nonzero buffer offset first.

**Definition 1.10 (paddedWord).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedWord`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenate the first input word, its constructed six-site buffer and the second input word.

**Theorem 1.11 (padded_word_injective).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_word_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_word_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both original preference words are recovered from their literal coordinates. This proves injectivity on words for every pair of lengths, independently of the chosen matching certificates. The full padded certificate and the cardinality theorem use this recovery without counting certificate witnesses.

**Theorem 1.12 (padded_buffer_top).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_buffer_top`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_buffer_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero buffer assignment in the actual padded preference word is first-ranked. The certificate proof uses this strict first rank on every nonmatching edge incident to a matched buffer endpoint.

**Definition 1.13 (bufferOffset).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.bufferOffset`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.bufferOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an occupied site reverse the actual old request. At every unoccupied site use the existing six-site mate, with displacement zero only for a single.

**Theorem 1.14 (buffer_offset_completion).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.buffer_offset_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.buffer_offset_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual signed buffer offsets simultaneously fulfill every incoming request, stay between -2 and 2, and allow only central singles. Every distinct buffer neighbor at distance at most two from a single has nonzero displacement. These bounds and isolation facts are consumed in the full padded certificate. CyclicClosure uses the same buffer facts for its actual source-cycle matching.

**Theorem 1.15 (closing_coordinate).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closing_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closing_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact buffer coordinate is target+6 for a left exterior request and target-m for a right exterior request. The full integer-coordinate identity is retained for source-cycle transport.

**Definition 1.16 (oldRanking).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldRanking`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldRanking` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Preserve the old rankings on both separated pieces.

**Theorem 1.17 (old_nonblocking).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.old_nonblocking`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.old_nonblocking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every old--old edge has its original stability test. The six-site gap excludes cross-piece edges; translation preserves each same-piece rank comparison.

**Definition 1.18 (ClosingRequester).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.ClosingRequester`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.ClosingRequester` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select exterior nonzero requests of one certified word. No old single is reclassified as a request.

**Definition 1.19 (closingRequest).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closingRequest`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closingRequest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map left exterior targets to buffer sites 4,5 and right exterior targets to 0,1. This retains the four distinct possible exterior targets even at m=1.

**Theorem 1.20 (closing_request_completion).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closing_request_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closing_request_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every length, actual closing requests are injective and avoid central sites. The existing sixteen layouts fulfill all requests with a genuine involution and only central new singles. CyclicClosure supplies full source-cycle stability, including m=1 extra buffer wrap edges, and injectivity on closed preference profiles.

**Definition 1.21 (oldPosition).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldPosition`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldPosition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Place the left word at coordinates 0 through m-1 and the right word at m+6 through m+6+k-1.

**Definition 1.22 (oldOffset).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldOffset`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Preserve every chosen displacement in the two input certificates, including zero for singles.

**Definition 1.23 (oldTarget).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldTarget`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Targets are integers, including all exterior requests. No quotient or truncation removes possible collisions.

**Definition 1.24 (Requester).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.Requester`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.Requester` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select the actual old vertices whose nonzero requests enter the six-site gap.

**Definition 1.25 (request).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.request`

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.request` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translate each actual gap target to its buffer coordinate in Fin 6.

**Theorem 1.26 (old_target_injective).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.old_target_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.old_target_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full integer-target injectivity holds across both old pieces. Within one piece use its certificate; across pieces the left targets are at most m+1 and the right targets at least m+4.

**Theorem 1.27 (padded_request_completion).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_request_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_request_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual gap requests are injective and avoid the two central buffer sites. Apply the existing sixteen-layout construction to obtain a genuine involution on requesters plus buffer, with only central new singles. The full padded certificate additionally proves reciprocity on every old/new pair, injectivity of every integer target and all nonblocking tests.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.ClosingRequester`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.Requester`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.bufferIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.bufferOffset`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.buffer_offset_completion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.chosenOffset`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closingRequest`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closing_coordinate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.closing_request_completion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.count_padded_supermultiplicative`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldOffset`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldPosition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldRanking`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.oldTarget`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.old_nonblocking`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.old_target_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedBuffer`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedCertified`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedOffset`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.paddedWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_buffer_top`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_request_completion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.padded_word_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.partnerFirst`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion.request`
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/BufferLayout](BufferLayout.md)
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/OpenCertificates](OpenCertificates.md)
