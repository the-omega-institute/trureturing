# Constructing a matching from every accepted scan

## Abstract

Ordered endpoint queues decode every permitted rank into an actual perfect matching.

**Definition 1.1 (The general-rank queue algorithm).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decodePairs`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decodePairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Opening appends the current vertex. Closing pairs it with the selected queue entry and deletes that entry. The algorithm tests only the selected rank and final empty queue, without inspecting a source pattern.

**Theorem 1.2 (Exact endpoint coverage).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decode_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decode_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For equal-length vertex and action lists and a valid initial base whose old-plus-pending size equals the queue length, every accepted suffix decodes. Its concatenated pair endpoints are a permutation of the queue followed by the full unscanned vertex list.

**Definition 1.3 (Realization by a partner map).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.Realizes`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Decoder.Realizes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A realization follows the entire scan: an opening has a later partner, and a closing vertex has the selected queue entry as its actual partner. It assumes no avoidance law.

**Definition 1.4 (Recording the actual active rank).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.encodeFrom`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Decoder.encodeFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The deterministic encoder records openings and, at a closure, the index of the actual partner in the opener queue.

**Theorem 1.5 (Decoded pairs realize the complete scan).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decoded_realizes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decoded_realizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

With increasing queue and vertex lists, all queued vertices earlier than the remaining vertices, and a partner map realizing every decoded pair, the complete ranked scan is realized by that partner map.

**Theorem 1.6 (Recovery of all recorded ranks).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.realizes_encode`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Decoder.realizes_encode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Encoding any realization with the natural endpoint order recovers exactly the same ranked scan. The increasing queue has no duplicate opener, so its selected index is recovered uniquely.

**Definition 1.7 (The decoded actual perfect matching).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decodeMatching`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decodeMatching` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For a complete accepted scan, decode all vertices of Fin(2n) in increasing order. Exact endpoint coverage gives a list with no duplicate endpoint. Its partner map is an involution with no fixed point, using the generic disjoint-pair involution theorem.

**Theorem 1.8 (The constructed matching realizes its scan).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decode_realizes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decode_realizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The perfect matching decoded from any accepted scan realizes every action and selected opener of that full scan.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.Realizes`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decodeMatching`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decodePairs`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decode_pairs`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decode_realizes`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.decoded_realizes`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.encodeFrom`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Decoder.realizes_encode`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Machine](P13Machine.md)
