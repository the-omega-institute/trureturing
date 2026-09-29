# CayleyPy Conjecture One Refutation

## Abstract

A polynomial-size generator family with non-quasipolynomial Cayley diameter.

**Definition 1.1 (Products of at most three transpositions).**

Lean statement: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.tripleTranspositionProducts`

*Formalization.* `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.tripleTranspositionProducts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set contains exactly the products of lists of at most three swaps of Fin n, including the empty product.

**Theorem 1.2 (Triple-product diameter upper bound).**

Lean statement: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.tripleTranspositionProducts_diameter_upper`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.tripleTranspositionProducts_diameter_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every permutation of Fin n is factored into at most n transpositions. Grouping factors in blocks of at most three gives a Cayley diameter at most (n + 2) / 3 with integer division.

**Theorem 1.3 (Separated square and nonsquare slopes).**

Lean statement: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.not_eventuallyQuasipolynomial_of_square_diameter_gap`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.not_eventuallyQuasipolynomial_of_square_diameter_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In one residue class, large squares and nearby nonsquares force a proposed constituent polynomial onto opposite sides of the line 5n/12. A polynomial has a fixed eventual sign relative to that line.

**Definition 1.4 (Square-dependent generator family).**

Lean statement: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.conjectureOneGenerators`

*Formalization.* `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.conjectureOneGenerators` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At square sizes the generators are products of at most three transpositions; at other sizes they are all transpositions.

**Definition 1.5 (Square-dependent Cayley diameter).**

Lean statement: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.conjectureOneDiameter`

*Formalization.* `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.conjectureOneDiameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational-valued function is the diameter of the undirected multiplicative Cayley graph of the square-dependent generators.

**Theorem 1.6 (Refutation of CayleyPy Growth Conjecture 1).**

Lean statement: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.cayleyPy_conjecture1_refuted`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.cayleyPy_conjecture1_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Chervov and others (2025). *CayleyPy Growth: Efficient growth computations and hundreds of new conjectures on Cayley graphs*. DOI: [10.48550/arXiv.2509.19162](https://doi.org/10.48550/arXiv.2509.19162). URL: <https://arxiv.org/abs/2509.19162v2>.

*Commentary.*

At square sizes use products of at most three transpositions; otherwise use all transpositions. Both generator sets have polynomial-size explicit enumerations. The full-support rotation gives the nonsquare lower bound, and the triple-product bound gives the square upper bound. The output-time estimate is discharged outside Lean.

## References

- Truth anchor: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.cayleyPy_conjecture1_refuted`
- Truth anchor: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.conjectureOneDiameter`
- Truth anchor: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.conjectureOneGenerators`
- Truth anchor: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.not_eventuallyQuasipolynomial_of_square_diameter_gap`
- Truth anchor: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.tripleTranspositionProducts`
- Truth anchor: `D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation.tripleTranspositionProducts_diameter_upper`
- Dependency: [D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation](QuasipolynomialWordMetricRefutation.md)
