# Catalan-Fibonacci enumeration above the boundary

## Abstract

The height-two suffix series is expressed by Catalan shapes and Fibonacci phase weights.

**Theorem 1.1 (The Catalan-Fibonacci continuation formula).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsBulk.bulk_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsBulk.bulk_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

With x counting scan actions, the normal-phase suffix series at height two equals xH(x^2) times the normal-phase suffix series at height one. The transition matrix D = ((1,1),(1,0)) retains both phases above height two. Its kth power weights the Cat_k excursion shapes, and the exit vector (2,1) gives the Fibonacci factor F_{k+3}.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsBulk.bulk_enumeration`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsWordSeries](TripleAvoidingMatchingsWordSeries.md)
