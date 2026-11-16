# The source graph and its anchored initial cycle

## Abstract

The source graph and its anchored initial cycle.

**Definition 1.1 (Value-labelled inversion graph).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Graph.valueGraph`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62Graph.valueGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

The vertices are zero-based representatives u of the values u+1. Two vertices u,v are adjacent precisely when ((u+1)-(v+1)) times ((pi inverse(u)+1)-(pi inverse(v)+1)) is negative. Both differences and the product are evaluated in the integers.

**Theorem 1.2 (Order form of source adjacency).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Graph.value_adj`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Graph.value_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

Adjacency is equivalent to u < v with pi inverse(v) < pi inverse(u), or the reverse inequalities. Adding one to both value labels and position labels cancels in the two integer differences.

**Theorem 1.3 (An initial cycle through both anchors).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62Graph.anchored_start`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62Graph.anchored_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

For every n >= 3 and permutation pi, assume that the value-labelled inversion graph is connected and remains connected after every vertex deletion. Then some triangle or 3412 starts an ear run containing both the original leftmost and bottommost points. Two distinct neighbours force the first value and the position of the minimum to be at least two in zero-based coordinates. An intermediate point below the first value yields the triangle. Otherwise positions 0,1,pi inverse(0),pi inverse(1) yield the 3412.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Graph.anchored_start`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Graph.valueGraph`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62Graph.value_adj`
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62Representation](Verkama62Representation.md)
