# Encoding matchings by labeled scan actions

## Abstract

Three distinct actions record openings and the two possible closing ranks of an avoiding matching.

**Definition 1.1 (The three scan actions).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.Action`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.Action` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The alphabet has three distinct letters: opening, oldest and second. The last two distinguish closing the oldest open arc from closing the second-oldest open arc, including when only two arcs are open.

**Definition 1.2 (The scan word of a matching).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.encode`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.encode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

At each vertex, record opening if its partner lies to the right. Otherwise record second if some older arc remains open at that vertex, and oldest if no such older arc exists. For a P1-avoiding matching these labels specify the exact closing rank.

**Theorem 1.3 (The scan word determines an avoiding matching).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.encode_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.encode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Two P1-avoiding perfect matchings on the same 2n ordered vertices are equal whenever their encoded action words are equal. The order of the open arcs determines each closing partner from its action label.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.Action`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.encode`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsEncoding.encode_injective`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsScan](TripleAvoidingMatchingsScan.md)
