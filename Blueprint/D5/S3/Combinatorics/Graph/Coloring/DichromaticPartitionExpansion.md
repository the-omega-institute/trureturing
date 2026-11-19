# Dichromatic polynomial and vertex partitions

## Abstract

Acyclic colourings of a finite digraph give a falling-factorial expansion.

Crew, Keller, Kuehr, Lin, Monroy Rodríguez and Williams define the dichromatic polynomial by acyclic colourings in Properties of the Dichromatic Polynomial, Section 2. Section 8.1, Conjecture 2 concerns its ratio to the power of the palette size. https://arxiv.org/html/2611.13273v1

**Definition 1.1 (Acyclic induced digraphs).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.AcyclicOn`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.AcyclicOn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

An induced digraph has no injectively indexed cyclic sequence following its arcs. Sequences of lengths one and two detect loops and digons.

**Definition 1.2 (Acyclic colour maps).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.AcyclicColoring`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.AcyclicColoring` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

Each inverse image of a palette name induces an acyclic digraph. Unused names have empty inverse image.

**Definition 1.3 (Unlabelled acyclic blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.IsAcyclic`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.IsAcyclic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

Every block of a finite partition of all the vertices induces an acyclic digraph.

**Definition 1.4 (Real partition weights).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.partitionWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.partitionWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

The weight of a partition with k blocks on n vertices is the falling factorial of x of length k divided by the nth power of x.

**Definition 1.5 (Falling-factorial expansion).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial`

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

Sum the real falling-factorial polynomial of degree k over acyclic partitions with k blocks.

**Theorem 1.6 (Integer evaluations count colour maps).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.eval_dichromaticPolynomial_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.eval_dichromaticPolynomial_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

For every natural palette size q, the evaluation is the number of acyclic maps into Fin q. A colour map yields its nonempty fibres and an injection from these fibres to the palette. An acyclic partition and such an injection recover the map. Counting the injections gives one falling factorial for each partition.

**Theorem 1.7 (Uniqueness from natural palette sizes).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.eq_dichromaticPolynomial_of_eval_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.eq_dichromaticPolynomial_of_eval_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

Agreement at every natural palette size gives infinitely many real evaluation points. A polynomial satisfying the colouring count is therefore the dichromatic polynomial.

**Theorem 1.8 (The normalized polynomial as a sum over partitions).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_div_eq_sum_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_div_eq_sum_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

The ratio of the dichromatic polynomial to the nth power of x is the sum of the weights of the acyclic partitions.

**Theorem 1.9 (Refining acyclic blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.isAcyclic_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.isAcyclic_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

Each block of a finer partition is contained in a block of the coarser partition. Any cycle in a finer block would be a cycle in its containing block.

**Theorem 1.10 (The entire digraph is acyclic).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_eq_pow_of_acyclic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_eq_pow_of_acyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

All maps into a palette of size q are acyclic. Their number is q to the power n, which determines the polynomial.

**Theorem 1.11 (A loop forces the zero polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_eq_zero_of_loop`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_eq_zero_of_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

The fibre containing a loop vertex contains that loop at every palette size.

**Theorem 1.12 (Orders zero and one).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_small`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_small` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

At orders zero and one the polynomial is the nth power of the variable for an acyclic digraph, and zero if there is a loop. Injectivity bounds the length of a cycle by n.

**Theorem 1.13 (Partition weights sum to one).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.sum_partitionWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.sum_partitionWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

The empty-arc digraph admits every partition and every colour map. Dividing its polynomial by the nonzero normalizing power gives total weight one.

**Theorem 1.14 (Nonnegative weights on the real interval).**

Lean statement: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.partitionWeight_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.partitionWeight_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lila Crew, Benjamin Keller, Katharina Kuehr, Shao Yuan Lin, Megan Ixchel Monroy Rodríguez, Tabitha Williams (2026). *Properties of the Dichromatic Polynomial*. DOI: [10.48550/arXiv.2611.13273](https://doi.org/10.48550/arXiv.2611.13273). URL: <https://arxiv.org/abs/2611.13273v1>.

*Commentary.*

For n at least two and x at least n minus one, each falling factorial is nonnegative because its length is at most n. The normalizing power is positive.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.AcyclicColoring`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.AcyclicOn`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.IsAcyclic`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_div_eq_sum_weight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_eq_pow_of_acyclic`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_eq_zero_of_loop`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.dichromaticPolynomial_small`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.eq_dichromaticPolynomial_of_eval_nat`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.eval_dichromaticPolynomial_nat`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.isAcyclic_of_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.partitionWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.partitionWeight_nonneg`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/DichromaticPartitionExpansion.sum_partitionWeight`
