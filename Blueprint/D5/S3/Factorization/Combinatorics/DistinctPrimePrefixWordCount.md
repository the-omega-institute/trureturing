# Distinct Initial Labels in Occupation Words

## Abstract

Distinct Initial Labels in Occupation Words.

**Theorem 1.1 (Counting words with a distinct prefix).**

Lean statement: `D5/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount.distinct_prefix_count_factorial`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount.distinct_prefix_count_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a finite multiset of labels, let r be its cardinality, and let j lie between zero and r. Count the words with occupation a whose first j labels are pairwise distinct. Multiplying this count by the product of the multiplicity factorials gives j! times (r-j)! times the elementary symmetric coefficient of degree j in the multiplicities. The formula includes zero multiplicities and the empty word. Partitioning each word at position j and then by its set of initial labels gives the count.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount.distinct_prefix_count_factorial`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../../Quantum/Entanglement/OccupancyWordSectors.md)
