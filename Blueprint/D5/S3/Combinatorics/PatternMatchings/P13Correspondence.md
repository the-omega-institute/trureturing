# The full P13 matching and scan correspondence

## Abstract

Explicit normalized local scans and actual P13-avoiding perfect matchings are equivalent for every nonnegative size.

**Definition 1.1 (The complete active opener set).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.QueueAt`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.QueueAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

At cut t, the ordered queue contains exactly the vertices x<t whose partners are at least t.

**Definition 1.2 (The complete remaining endpoint set).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.VerticesAt`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.VerticesAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The unscanned suffix contains exactly the vertices at least t.

**Theorem 1.3 (Total encoding at every size).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.encode_realizes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.encode_realizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Scanning any actual perfect matching with its complete ordered queue and remaining vertex suffix realizes the whole ranked scan. Every selected closing rank is in range, and insertion and deletion preserve increasing opener order.

**Definition 1.4 (The local law at one closure).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.FutureAt`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.FutureAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Among surviving active openers x<y, x closes before y exactly when the just-closed opener lies between them.

**Definition 1.5 (The law at every remaining closure).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.FutureSuffix`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.FutureSuffix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Every vertex at or after the cut satisfies the exact local future-order law.

**Theorem 1.6 (Scan orders are exactly the actual future laws).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.ordered_run_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.ordered_run_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For the complete active queue and remaining endpoint suffix of an actual matching, realization of every scan order is equivalent to the future-order law at all remaining closures.

**Theorem 1.7 (Every P13 avoider is accepted).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.encode_accepted`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.encode_accepted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The full ranked encoding of every actual P13-avoiding matching is accepted from the empty normalized base with no pending openings.

**Theorem 1.8 (Every accepted scan produces a P13 avoider).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.decode_avoids`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.decode_avoids` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The actual perfect matching decoded from any complete accepted scan avoids the source set P13. All imposed survivor orders persist and the exact source-pattern criterion applies.

**Theorem 1.9 (The complete scan determines all partners).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.realizes_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.realizes_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Two actual matchings realizing the same ranked scan agree on every queued or remaining endpoint, including the endpoints paired at each closure.

**Definition 1.10 (The unbounded carrier equivalence).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.matchingEquiv`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.matchingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every n>=0, actual P13-avoiding perfect matchings of Fin(2n) are equivalent to scans accepted by the independent normalized local machine. Encoding and decoding are total inverses. The empty matching is included, and scans may return to zero and start another component. This structural correspondence does not state the enumeration or a generating function.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.FutureAt`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.FutureSuffix`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.QueueAt`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.VerticesAt`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.decode_avoids`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.encode_accepted`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.encode_realizes`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.matchingEquiv`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.ordered_run_iff`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.realizes_unique`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Orders](P13Orders.md)
