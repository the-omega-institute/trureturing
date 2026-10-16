# Actual primitive cyclic blocks

## Abstract

FiniteCyclicBlocks

ClosedClass(P) denotes the actual closed class of the original finite real row-stochastic matrix. ClassPeriods(P,C) carries its genuine positive return-time gcd p and the surjective cyclic map phi. Phase(K,j) is the subtype of states in C whose label equals j. block(K,j) is the actual restriction of A^p to this subtype, where A=restriction(P,C). It uses Subtype.val in both coordinates.

**Theorem 1.1 (Actual primitive cyclic blocks).**

$$\forall X:Type, ([\operatorname{Fintype}(X)][\operatorname{DecidableEq}(X)]\forall P:\operatorname{Matrix}(X, X, \mathbb{R}), (\operatorname{RowStochastic}(P)\implies \forall C:\operatorname{ClosedClass}(P), (\exists K:\operatorname{ClassPeriods}(P, C), \operatorname{Blocks}(K))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteCyclicBlocks.actual_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Blocks(K) asserts for every j that Phase(K,j) is nonempty, block(K,j) is row stochastic and Matrix.IsPrimitive, and for every n and x,y in Phase(K,j), (block(K,j)^n)(x,y)=(P^(p*n))(x,y) using both original state projections. For every distinct actual closed class D, every natural n, x in D and y in C, the ambient (P^n)(x,y) is zero.

The residue law forces every p-step transition to stay in its phase. Summing the actual stochastic A^p row over that phase therefore preserves the row sum one. The same zero entries justify each multiplication of restricted blocks and yield their exact ambient power identity. Finite uniformization of the proved eventual allowed-residue positivity gives a strictly positive power of each actual phase block. No primitivity certificate or chosen partition is a premise.

Distinct-class zero entries use the actual disjointness and no-exit fields of FiniteClosedClasses.actual_structure. The period and the matrix restriction come from the original P throughout. These blocks supply the primitive mixing theorem for actual closed-class limits. Transient entry-time convolution and the simultaneous rational denominator remain separate assertions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteCyclicBlocks.actual_blocks`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteGenuinePeriods](FiniteGenuinePeriods.md)
