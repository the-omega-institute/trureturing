# Transporting total orders through queue deletion

## Abstract

One common closing-time function realizes every comparison imposed by an accepted normalized scan.

**Definition 1.1 (Old base constraints).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.Respects`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Orders.Respects` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A closing-time function respects all comparisons among old survivors in the normalized base; it imposes no comparison on pending openings.

**Definition 1.2 (The order imposed by one closure).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.ClosureRespects`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Orders.ClosureRespects` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Every two surviving queue entries close in the order prescribed by the two blocks on opposite sides of the selected rank.

**Theorem 1.3 (Every comparison is determined).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.closure_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Orders.closure_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A closing-time function respecting the full imposed survivor order compares any two survivor times exactly according to that order, in both directions.

**Theorem 1.4 (Order transport across actual queue deletion).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.deletion_order`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Orders.deletion_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For an in-range closing rank, realization of the new normalized base on the queue after deletion is equivalent to realization of the full imposed order on the original survivors.

**Theorem 1.5 (Necessity of all old constraints).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.compatible_of_orders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Orders.compatible_of_orders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

If the same closing-time function realizes the old base, the new closure order and the current selected opener as the first closure, then all old comparisons are compatible with the new order.

**Theorem 1.6 (Sufficiency for all old constraints).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.respects_of_compatible`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Orders.respects_of_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Compatibility, the realized new survivor order and the selected opener as the first closure together imply every comparison of the old base, including those involving the opener just removed.

**Definition 1.7 (All orders of a complete scan).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.OrderedRun`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Orders.OrderedRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

At each closure the survivor closing times realize the imposed total two-block order; openings add no comparison.

**Theorem 1.8 (Exhaustive arbitrary-size normalization).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Orders.normalized_run`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Orders.normalized_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For any actual matching realizing an ordered scan, local acceptance from a valid old base and a separate pending count is equivalent to realization of the old base and every subsequently imposed closure order. Each induction step uses the same actual closing times, so earlier constraints remain compatible throughout the scan.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.ClosureRespects`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.OrderedRun`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.Respects`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.closure_comparison`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.compatible_of_orders`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.deletion_order`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.normalized_run`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Orders.respects_of_compatible`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Decoder](P13Decoder.md)
