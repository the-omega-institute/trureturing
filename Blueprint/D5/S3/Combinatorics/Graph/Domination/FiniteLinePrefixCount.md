# Uniform counting of finite line prefixes

## Abstract

Uniform counting of finite line prefixes

**Definition 1.1 (Actual tuples with distinct column labels).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount.Prefix`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount.Prefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let V be finite, let L_j be prescribed finite subsets of V, and let c map vertices to a label type. A prefix of length k is a function f from Fin k to V such that f(i) belongs to L_i and the labels c(f(i)) are pairwise distinct. These are actual finite tuples, with no recursively defined substitute for their cardinality.

**Theorem 1.2 (A uniform lower bound at every prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount.card_prefix_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount.card_prefix_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural m and K, suppose c is injective on every L_j and the cardinality of L_j is at least m+j for every j<K. Then the number of prefixes of length K is at least m^K. For a fixed prefix of length j, its used labels forbid at most j vertices of L_j, leaving at least m choices. Appending a legal vertex is injective on the dependent pair consisting of that prefix and its next choice. Summing these fiber cardinalities and inducting on j gives the bound. The lower bound holds for every prefix on the same family; it does not multiply separately attainable optima.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount.Prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount.card_prefix_lower_bound`
