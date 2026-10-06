# All-direction partitions of mixed-alphabet Hamming graphs

## Abstract

Every mixed-alphabet Hamming graph in at least four dimensions admits a partition into maximal full coordinate lines using every direction.

**Definition 1.1 (Mixed vertices).**

Lean statement: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.Vertex`

*Formalization.* `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.Vertex` (`✓ std3`).

*Citation.* Nasra Daher Ahmed, Ravi Kunjwal (2026). *Characterizing unitaries via quasi-process functions*. DOI: [10.48550/arXiv.2610.00579](https://doi.org/10.48550/arXiv.2610.00579). URL: <https://arxiv.org/html/2610.00579v1>.

*Commentary.*

For each coordinate i in Fin n, the vertex independently chooses an element of Fin (d i). Alphabet sizes may differ.

**Definition 1.2 (Hamming adjacency).**

Lean statement: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.graph`

*Formalization.* `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.graph` (`✓ std3`).

*Citation.* Nasra Daher Ahmed, Ravi Kunjwal (2026). *Characterizing unitaries via quasi-process functions*. DOI: [10.48550/arXiv.2610.00579](https://doi.org/10.48550/arXiv.2610.00579). URL: <https://arxiv.org/html/2610.00579v1>.

*Commentary.*

Vertices are adjacent exactly when they disagree in one coordinate and agree in every other coordinate.

**Definition 1.3 (Full coordinate lines).**

Lean statement: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.line`

*Formalization.* `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.line` (`✓ std3`).

*Citation.* Nasra Daher Ahmed, Ravi Kunjwal (2026). *Characterizing unitaries via quasi-process functions*. DOI: [10.48550/arXiv.2610.00579](https://doi.org/10.48550/arXiv.2610.00579). URL: <https://arxiv.org/html/2610.00579v1>.

*Commentary.*

The full line in direction i through x fixes x in every coordinate except i. The coordinate i ranges over its entire alphabet.

**Theorem 1.4 (Ahmed–Kunjwal Conjecture V.1).**

Lean statement: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.result` (`✓ std3`). ∎

*Resolves.* `Problems/ahmed-kunjwal-2026-hamming-multipartite-partition` (proved) by `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ahmed-kunjwal-2026-hamming-multipartite-partition","declaration_gid":"D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nasra Daher Ahmed, Ravi Kunjwal (2026). *Characterizing unitaries via quasi-process functions*. DOI: [10.48550/arXiv.2610.00579](https://doi.org/10.48550/arXiv.2610.00579). URL: <https://arxiv.org/html/2610.00579v1>.

*Commentary.*

For every natural n at least four and every independent alphabet-size function d with d(i) at least two, there is a family P of nonempty sets of vertices. Every vertex belongs to exactly one member. Every member is a full coordinate line and an inclusion-maximal clique of the Hamming graph. Every coordinate i is the direction of some full line in P.

A private four-dimensional binary selector is checked by kernel reduction. Its selected coordinate is stable under flipping that coordinate. Induction adds a coordinate by replacing one binary edge with vertical edges; a second edge in the distinguished direction supplies the next two reserves. Every other direction survives because its selector value differs.

For mixed alphabets, zero maps to false and every positive symbol maps to true. The binary selector is constant along the entire selected mixed line, including all positive symbols. Fixing the actual off-direction coordinates splits each binary edge preimage into full lines. Constancy gives unique family membership. An outsider disagrees off the direction, and a line point can also disagree in the direction, proving inclusion-maximality.

The source attributes the binary case to Erde; that case is not claimed as new. The physics interpretation, optimal counts, and exhaustive literature priority are not formalized. This is an original Apache-2.0 Lean implementation by OpenAI Codex (GPT-6), using the pinned Mathlib APIs. Independent review, repository admission, and required CI remain separate gates.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.graph`
- Truth anchor: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.line`
- Truth anchor: `D5/S3/Combinatorics/Hamming/HammingMultipartitePartition.result`
