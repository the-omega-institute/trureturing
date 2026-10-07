# The future order of arcs avoiding P13

## Abstract

Source avoidance determines exactly the relative closing order of the active survivors.

**Definition 1.1 (The source pattern set).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Local.P13`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Local.P13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The source labels are 132, 213 and 321, written as zero-based vectors. Their labels record complementary right-endpoint ranks.

**Definition 1.2 (Avoidance by an actual perfect matching).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Local.Avoids`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Local.Avoids` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

An actual perfect matching avoids each of the three source patterns. An occurrence requires three increasing left endpoints preceding every one of the three right endpoints.

**Definition 1.3 (Chronological closing words).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Local.ClosingOccurs`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Local.ClosingOccurs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

An eligible triple is indexed by increasing opener. The displayed word gives these indices in increasing order of their right endpoints. Source 132 corresponds to closing word 231, source 213 to 312, and source 321 to 123.

**Definition 1.4 (The pairwise future-order law).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Local.FutureOrder`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Local.FutureOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

At a closure, consider two surviving active openers x<y. The older one closes before the younger one exactly when the opener just selected lies strictly between them.

**Theorem 1.5 (Exact local characterization).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Local.future_order_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Local.future_order_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every perfect matching of Fin(2n), P13 avoidance is equivalent to the future-order law at every closure. The eligibility condition ensures that any two survivors and the just-closed arc form a source triple; conversely each forbidden eligible triple violates the law at its first closure.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Local.Avoids`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Local.ClosingOccurs`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Local.FutureOrder`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Local.P13`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Local.future_order_iff`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder](TripleAvoidingMatchingsDecoder.md)
