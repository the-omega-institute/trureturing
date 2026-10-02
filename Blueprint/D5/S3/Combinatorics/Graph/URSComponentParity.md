# Component parity of uniform reflection arrays

## Abstract

Fix one indexed array of 2n permutation rows on n columns and n symbols. Fibres and joint counts refer to this same array and its original row indices. For odd n at least three, fibre size two and equality of reflected joint counts force its fibre graph to be connected. The conclusion also applies to arrays whose first row is the identity and whose rows are sorted on their original labels.

**Definition 1.1 (Actual column-symbol fibres).**

Lean statement: `D5/S3/Combinatorics/Graph/URSComponentParity.fibre`

*Formalization.* `D5/S3/Combinatorics/Graph/URSComponentParity.fibre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a column x and symbol p, the fibre F(x,p) consists of precisely the row indices i for which the permutation in row i sends x to p.

**Definition 1.2 (Actual joint counts).**

Lean statement: `D5/S3/Combinatorics/Graph/URSComponentParity.pairCount`

*Formalization.* `D5/S3/Combinatorics/Graph/URSComponentParity.pairCount` (`✓ std3`).

*Citation.* Enrico Iurlano, Günther R. Raidl (2026). *Pairwise Reflection Symmetry in Generalized Latin Rectangles*. DOI: [10.48550/arXiv.2606.28315](https://doi.org/10.48550/arXiv.2606.28315). URL: <https://arxiv.org/html/2606.28315v1>.

*Commentary.*

The count f(x,y;p,q) is the number of actual row indices i sending x to p and y to q simultaneously, as in Definition 3 of the source. All counts use the same row family.

**Definition 1.3 (The graph on original row indices).**

Lean statement: `D5/S3/Combinatorics/Graph/URSComponentParity.fibreGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/URSComponentParity.fibreGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Distinct row indices i and j are adjacent precisely when some column has the same symbol in both rows. Under the fibre-size-two hypothesis these are exactly the pairs making up the actual fibres.

**Theorem 1.4 (Odd order forces connectivity).**

Lean statement: `D5/S3/Combinatorics/Graph/URSComponentParity.fibre_graph_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/URSComponentParity.fibre_graph_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Enrico Iurlano, Günther R. Raidl (2026). *Pairwise Reflection Symmetry in Generalized Latin Rectangles*. DOI: [10.48550/arXiv.2606.28315](https://doi.org/10.48550/arXiv.2606.28315). URL: <https://arxiv.org/html/2606.28315v1>.

*Commentary.*

The source domain is URS(n,2,1), abbreviated URS(n,2), in Definition 4, with reflection symmetry from Definition 3. Definition 2 restricts to reduced arrays by requiring an identity first row and lexicographic row order. The repository-derived connectivity theorem applies to the full domain without these reduction conditions.

For every odd n at least three and every indexed family of 2n permutations on Fin n, assume each column-symbol fibre has exactly two row indices and f(x,y;p,q)=f(x,y;q,p) whenever x and y are distinct columns and p and q are distinct symbols. Then the actual fibre graph is connected. Identity-first and lexicographic sorting conditions are unnecessary for this conclusion.

A proper set S closed under fibre edges has size 2s, with exactly s occupied symbols in every column. An actual row i outside S defines a graph on the columns: x is adjacent to y when the symbol in row i at y is occupied by S at x. Reflection supplies an actual row with the two outside-row symbols exchanged, which proves symmetry of this graph. Its diagonal is empty and every degree is s. The handshaking lemma on the odd column set forces s even, so four divides the size of S. If the fibre graph were disconnected, one component and its complement would both have size divisible by four, contradicting the oddness of n.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/URSComponentParity.fibre`
- Truth anchor: `D5/S3/Combinatorics/Graph/URSComponentParity.fibreGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/URSComponentParity.fibre_graph_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/URSComponentParity.pairCount`
