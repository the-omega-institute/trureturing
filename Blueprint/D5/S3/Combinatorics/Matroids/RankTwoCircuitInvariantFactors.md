# Invariant factors of the rank-two lifting obstruction

## Abstract

The cyclic factors of the rank-two integral lifting quotient.

**Theorem 1.1 (The invariant factors for parallel classes).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors.rank_two_lifting_obstruction_invariant_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors.rank_two_lifting_obstruction_invariant_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a loopless rank-two matroid have k + 2 nonempty parallel classes, a ground of size n and class sizes with gcd g. The lifting obstruction is the product of a cyclic group of order g and k cyclic groups of order n. A unimodular change of coordinates reduces the class-size relation to multiplication by the gcd of the weights outside the distinguished class. On the n-torsion subgroup this gcd imposes exactly the g-torsion condition. This also gives the two-class formula and the case of all singleton classes.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors.rank_two_lifting_obstruction_invariant_factors`
- Dependency: [D5/S3/Combinatorics/Matroids/RankTwoCircuitTorsion](RankTwoCircuitTorsion.md)
