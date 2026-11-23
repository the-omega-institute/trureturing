# Fibers of Ternary Point Potentials

## Abstract

Consider a finite point set with listed triples of distinct points. Each pair of distinct points lies in at most one indexed triple.

**Theorem 1.1 (Surjectivity, equal fibers and affine lines in the equality case).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers.point_potential_evaluations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers.point_potential_evaluations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an anchor. Let d be the dimension of the normalized ternary point-potential space. Evaluation in basis coordinates reaches every ternary vector of dimension d. Any two fibers are equivalent, so the point count is three to the power d times the size of the zero fiber. When two evaluation vectors differ, the pair belongs to an indexed triple whose third vector is their negative sum. If the point count equals three to the power d, evaluation is injective. The triples then correspond exactly to the triples of distinct vectors with zero sum, which are the affine lines over the ternary field. For two different fibers, fixing a point in the negative-sum fiber gives an involution that exchanges them by taking the third point.

**Theorem 1.2 (The additional ternary multiplicity divides the ground-set size in powers of three).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers.rank_three_lifting_obstruction_divisibility`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers.rank_three_lifting_obstruction_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a rank-three core on a finite ordered set of n greater than three points with singleton parallel classes, and suppose its bases are precisely the triples outside a family of m omitted triples satisfying the pair bound. The integral lifting obstruction is linearly equivalent over the integers to the direct sum of binom(n minus two, two) minus m factors of order n and d factors of order three, with three to the power d dividing n. The equal sizes of the potential fibers give this divisibility when n is divisible by three. When n is coprime to three, the potential count is one and d is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers.point_potential_evaluations`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers.rank_three_lifting_obstruction_divisibility`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials](RankThreeOmissionPotentials.md)
