# Avoiding matchings yield accepted scan words

## Abstract

The scan of every P1-avoiding perfect matching obeys the height and phase transitions.

**Theorem 1.1 (Acceptance of the encoded matching).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsAcceptance.encode_accepted`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsAcceptance.encode_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every P1-avoiding perfect matching on 2n ordered vertices, its encoded action word is accepted from height zero in the normal phase. The pending oldest closure persists through all intervening openings and disappears when that oldest arc closes.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsAcceptance.encode_accepted`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder](TripleAvoidingMatchingsDecoder.md)
