# Decoding accepted action words into perfect matchings

## Abstract

An ordered queue turns accepted action words into pairs covering every vertex exactly once.

**Definition 1.1 (Acceptance at a given height and phase).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.AcceptFrom`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.AcceptFrom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A state consists of a nonnegative height h and a phase indicating whether an oldest closure is required. An opening increases h and preserves the phase. An oldest closure requires positive height, decreases h by one and clears the phase. A second closure requires the normal phase and height at least two; it decreases h by one and sets the required phase exactly when the preceding height was at least three. The empty suffix is accepted exactly at height zero in the normal phase.

**Definition 1.2 (Accepted words of prescribed length).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.Accepted`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.Accepted` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For a nonnegative integer n, Accepted(n) consists of action words of length 2n accepted from height zero in the normal phase. The two closing letters remain distinct.

**Definition 1.3 (Pairing vertices with an ordered queue).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decodePairs`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decodePairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

An opening appends the current vertex to the queue. An oldest closure pairs the current vertex with the first queued vertex and removes that vertex. A second closure pairs it with the second queued vertex, retaining the first. Decoding succeeds at the end exactly when the queue and the remaining vertex and action lists are empty; incompatible lists give no pairing.

**Theorem 1.4 (Every accepted word yields all endpoint pairs).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decode_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decode_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Let q be an initial queue and let vs be an unscanned vertex list of the same length as an action word w. If w is accepted from height equal to the length of q in either phase, decoding produces a pair list whose concatenated endpoints are a permutation of q followed by vs.

**Definition 1.5 (The partner map of a pair list).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.pairFunction`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.pairFunction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For a list of pairs, the partner map exchanges the two endpoints of the first pair containing the argument. Vertices absent from every pair are fixed.

**Theorem 1.6 (Disjoint endpoint pairs give an involution).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.pairFunction_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.pairFunction_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

If the concatenated endpoints of a pair list have no repetitions, its partner map is an involution. A vertex is fixed exactly when it does not occur among those endpoints.

**Definition 1.7 (The matching decoded from an accepted word).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decodeMatching`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decodeMatching` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Decode an accepted word of length 2n using the empty initial queue and the vertices in increasing order. The resulting endpoint pairs cover each vertex exactly once, and their partner map defines a perfect matching.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.AcceptFrom`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.Accepted`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decodeMatching`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decodePairs`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.decode_pairs`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.pairFunction`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder.pairFunction_spec`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding](TripleAvoidingMatchingsEncoding.md)
