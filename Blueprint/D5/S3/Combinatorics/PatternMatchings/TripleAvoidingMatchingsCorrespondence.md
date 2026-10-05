# A bijection between avoiding matchings and accepted words

## Abstract

Encoding and queue decoding are inverse maps between P1-avoiding matchings and accepted action words.

**Definition 1.1 (The matching-word correspondence).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsCorrespondence.matchingEquiv`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsCorrespondence.matchingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every nonnegative integer n, the P1-avoiding perfect matchings on 2n ordered vertices are in bijection with the accepted action words of length 2n. The forward map records the scan actions, and the inverse pairs vertices with the ordered queue. Both closing choices at height two are retained.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsCorrespondence.matchingEquiv`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsAcceptance](TripleAvoidingMatchingsAcceptance.md)
