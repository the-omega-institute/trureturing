# Concrete completion decompositions

## Abstract

Literal P13 continuations retain the complete ranked vertex word at every height.

**Definition 1.1 (First closure survivor data).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.FirstClosureData`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Counts.FirstClosureData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The data records two survivor block sizes below d and a literal completion from their normalized base with d-1 closures. The first rank a must satisfy m at most a+1.

**Definition 1.2 (First closure bijection).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.firstClosureEquiv`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Counts.firstClosureEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For m positive, an initial run of k openings and its first legal rank uniquely give a and b, with k=a+b+1-m. The remaining suffix is a literal completion from blocks(a,b). The finite bounds follow from acceptance.

**Theorem 1.3 (Finite first closure count).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_first_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_first_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For m positive, c(m,d) is the finite sum over a and b below d of g(a,b,d-1), restricted to m at most a+1. Impossible block sizes have zero count.

**Definition 1.4 (Removing the first opening).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.emptySingleEquiv`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Counts.emptySingleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For positive d, a completion from the empty base starts with an opening. Removing that letter gives exactly a completion from S(1), and prepending it is the inverse.

**Theorem 1.5 (The empty base boundary).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_empty_single`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_empty_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For positive d, c(0,d) equals c(1,d).

**Theorem 1.6 (The empty completion).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_zero_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_zero_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The empty word is the unique zero degree completion from S(0).

**Theorem 1.7 (Separating the least legal rank).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_first_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_first_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For 1 at most m at most d, c(m,d) equals c(m+1,d) plus the sum over b below d of g(m-1,b,d-1). This separates the first closure rank m-1 from every larger rank.

**Theorem 1.8 (Closing only the old block).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The count c(m,m) is one. No new opening can occur, so the unique word closes the old block in descending rank order.

**Definition 1.9 (Actual P13 matching counts).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.actualCount`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Counts.actualCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The carrier is the P13 avoiding perfect matchings on Fin(2n), with the original source occurrence convention.

**Theorem 1.10 (Concrete triangular recurrence).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_triangular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_triangular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For 1 at most m at most d, c(m,d) equals c(m+1,d) plus c(m-1,d-1) plus the sum for j from 1 to d-m of choose(m+j-2,m-1)c(j,d-m). The forced prefix bijection and the first closure bijection give the recurrence, with support bounding every sum.

**Theorem 1.11 (Continuation recurrence for actual matchings).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Counts.actualCount_continuation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Counts.actualCount_continuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The actual matching carrier has one element for degree zero. For positive d, its count equals c(2,d) plus c(0,d-1) plus the sum of c(j,d-1) for j from 1 to d-1. The matching equivalence identifies the empty base continuation carrier with actual perfect matchings.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.FirstClosureData`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.actualCount`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.actualCount_continuation`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_diagonal`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_empty_single`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_first_difference`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_first_sum`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_triangular`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.c_zero_zero`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.emptySingleEquiv`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Counts.firstClosureEquiv`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Completions](P13Completions.md)
