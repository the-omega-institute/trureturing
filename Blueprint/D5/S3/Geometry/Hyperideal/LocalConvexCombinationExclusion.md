# A local convex-combination obstruction

## Abstract

Convexity of cosh excludes a local convex-combination flat candidate.

For a finite coordinate space, q, q1 and q2 are reading vectors and ell is a real length vector. The dot product records the actual pair length mean. If q is a convex combination of q1 and q2 with coefficient lambda in the unit interval, the convexity of cosh bounds the potential at q by the corresponding weighted sum.

Each cosh value is positive. The weighted sum is therefore at most the unweighted sum of the two endpoint potentials, while the flat-candidate inequality requires one additional unit. These inequalities are incompatible.

**Theorem 1.1 (Convex combinations cannot satisfy the flat candidate inequality).**

$$\forall n \in Nat,\; \forall q \in Function\left(Fin\left(n\right), Real\right),\; \forall q1 \in Function\left(Fin\left(n\right), Real\right),\; \forall q2 \in Function\left(Fin\left(n\right), Real\right),\; \forall ell \in Function\left(Fin\left(n\right), Real\right),\; \forall lambda \in Real,\; \left(0 \le lambda \land \left(lambda \le 1 \land \left(q = add\left(smul\left(lambda, q1\right), smul\left(1-lambda, q2\right)\right) \land 1+ cosh\left(dotProduct\left(q1, ell\right)\right)+ cosh\left(dotProduct\left(q2, ell\right)\right) \le cosh\left(dotProduct\left(q, ell\right)\right)\right)\right)\right) \Rightarrow False$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LocalConvexCombinationExclusion.local_convex_combination_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof derives the dot-product relation from the vector equality, applies the two-point Jensen inequality for cosh, and then uses positivity together with the coefficient bounds to contradict the required unit gap.

The statement applies to any finite real coordinate space and any real length vector. It records the local nonlinear obstruction only; it does not assert that every remaining acyclic candidate has a realization or that all low-degree candidates are eliminated.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LocalConvexCombinationExclusion.local_convex_combination_exclusion`
