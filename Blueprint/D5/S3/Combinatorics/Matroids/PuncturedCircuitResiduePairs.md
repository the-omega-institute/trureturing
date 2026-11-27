# Weighted Residue Pairs

## Abstract

The effect of a vanishing coordinate on a weighted pair of residues.

**Theorem 1.1 (Two weighted coordinates).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs.weighted_pair_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs.weighted_pair_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pair of residues is killed by the total size. Imposing a vanishing weighted sum of its two coordinates gives one factor of the common gcd of the total size and the two weights, and one factor of the total size.

**Theorem 1.2 (A distinguished pair with first coordinate zero).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs.punctured_pairs_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs.punctured_pairs_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a family of weighted pairs, force the first coordinate of one particular pair to vanish. That pair contributes one factor whose order is the gcd of the total size and the second weight. The other pairs retain both of their factors.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs.punctured_pairs_equiv`
- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs.weighted_pair_equiv`
- Dependency: [D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors](RankTwoCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms](UniformCircuitResidueForms.md)
