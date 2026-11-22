# Cyclic Factors for Sunflower Omissions

## Abstract

The joint lifting obstruction for omissions with a common element and pairwise disjoint petals.

**Theorem 1.1 (Cyclic Factors for Sunflower Omissions).**

Lean statement: `D5/S3/Combinatorics/Matroids/SunflowerCircuitInvariantFactors.sunflower_lifting_obstruction_invariant_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SunflowerCircuitInvariantFactors.sunflower_lifting_obstruction_invariant_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the full ground set have K elements and let 3 <= r < K. Fix a family of t sets of exactly r elements, all containing a fixed element e. A subset is a basis of the core if and only if it has exactly r elements and lies outside this family. The sets obtained by removing e from the omitted sets are pairwise disjoint. Use a finite block-ordered parallel expansion with a nonempty class over every ground element. Write n for its total size and g for the greatest common divisor of the class sizes. For each omitted set T, let q(T) be the greatest common divisor of n and the class sizes outside T. Put A = binom(K - 2, r - 2) and B = binom(K - 2, r - 1), and assume A >= t and B >= t. In the expanded matroid, let L be the image of the simultaneous circuit restriction map from the integral top-cycle lattice to the product of the integral top-cycle lattices of the contractions by its circuits. The component at a circuit C is the sum of the signed restrictions obtained by deleting each vertex of C in turn, using the insertion and shuffle signs. The saturation of L consists of the tuples in that product with a nonzero integer multiple in L. The saturation modulo L is isomorphic as an integer module to the direct sum of A - t cyclic groups of order g, B - t cyclic groups of order n and one cyclic group of order q(T) per omitted set. Induction uses the residue product identity, the single-omission formula and finite integral module cancellation.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SunflowerCircuitInvariantFactors.sunflower_lifting_obstruction_invariant_factors`
- Dependency: [D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors](PuncturedCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct](SunflowerCircuitResidueProduct.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors](UniformCircuitInvariantFactors.md)
- Dependency: [D5/S3/FiniteGroups/Modules/FiniteModuleProductCancellation](../../FiniteGroups/Modules/FiniteModuleProductCancellation.md)
