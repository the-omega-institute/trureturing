# The level-three and level-four obstruction in Q9

## Abstract

The level-three and level-four obstruction in Q9

**Theorem 1.1 (The missing triples cannot have the prescribed degrees).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_missing_triples`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_missing_triples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a family of thirty distinct triples of nine axes. The degree of a pair is the number of members of M containing it, and the degree of a four-set is the number of members of M it contains. Every pair having odd degree is incompatible with exactly fifty-four four-sets having degree one and no four-set having degree three.

Count ordered pairs of distinct missing triples meeting in two axes. Their union is a unique four-set and their intersection is a unique pair. In either count, a fibre of degree b contributes b(b−1). Each missing triple extends to six four-sets, so the sum of four-set degrees is 180. The four-set degrees are 0, 1, 2 or 4, and b(b−1) plus the indicator for b = 1 is congruent to b modulo eight. The ordered count is therefore congruent to 180 − 54 = 126, or 6 modulo eight.

Each missing triple contains three pairs, so the pair degrees sum to 90. Write each odd pair degree as b = 2t + 1. There are 36 pairs, giving a total of 27 for the t values. The identity b(b−1) = 6t + 4t(t−1) makes the ordered count congruent to 162, or 2 modulo eight. The two residues contradict each other.

**Theorem 1.2 (A 108-vertex balanced cubic support cannot occupy only levels three and four).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_balanced_cubic_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_balanced_cubic_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C be a 108-vertex subset of Q9 whose induced graph is cubic and whose signing satisfies BalancedCriticalSpectrum.IsBalanced. If every vertex of C has Boolean weight three or four, the degree sum across the two layers gives 54 vertices on each side.

The complement of the selected triples has thirty members among the 84 triples. A pair lies outside C, so exterior Huang cancellation leaves an even number of selected triple extensions among its seven extensions. Its missing degree is odd. A selected four-set has three selected triple neighbors by cubicity, hence missing degree one. An exterior four-set has even selected triple degree and therefore even missing degree. This gives exactly fifty-four four-sets of missing degree one and none of missing degree three.

This excludes a restricted component shape in Hong, Wu and Xia’s Problem 2. The full 258-vertex question remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_balanced_cubic_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction.no_missing_triples`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity](../SixtySixPointSupport/WeightLayerParity.md)
