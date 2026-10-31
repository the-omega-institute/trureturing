# Finite matroid intersection

## Abstract

Two matroids on a common finite ground have an attained intersection min-max equality.

**Theorem 1.1 (A common independent set and an attaining rank cut).**

$$\forall (alpha: Type_{u}), \forall (E: Set\left(alpha\right)), (\operatorname{Set}.\operatorname{Finite}\left(E\right)) \Rightarrow (\forall (M1: Matroid\left(alpha\right)), \forall (M2: Matroid\left(alpha\right)), (\operatorname{Matroid}.\operatorname{E}\left(M1\right) = E) \Rightarrow ((\operatorname{Matroid}.\operatorname{E}\left(M2\right) = E) \Rightarrow ((\exists (I: Set\left(alpha\right)), \exists (X: Set\left(alpha\right)), (I \subseteq E) \land ((X \subseteq E) \land ((\operatorname{Matroid}.\operatorname{Indep}\left(M1, I\right)) \land ((\operatorname{Matroid}.\operatorname{Indep}\left(M2, I\right)) \land (\operatorname{Set}.\operatorname{ncard}\left(I\right) = \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{Matroid}.\operatorname{eRk}\left(M1, X\right)\right) + \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{Matroid}.\operatorname{eRk}\left(M2, (E \setminus X)\right)\right)))))) \land (\forall (J: Set\left(alpha\right)), \forall (Y: Set\left(alpha\right)), (\operatorname{Matroid}.\operatorname{Indep}\left(M1, J\right)) \Rightarrow ((\operatorname{Matroid}.\operatorname{Indep}\left(M2, J\right)) \Rightarrow (\operatorname{Set}.\operatorname{ncard}\left(J\right) \le \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{Matroid}.\operatorname{eRk}\left(M1, Y\right)\right) + \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{Matroid}.\operatorname{eRk}\left(M2, (E \setminus Y)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/FiniteIntersection.finite_matroid_intersection` (`✓ std3`). ∎

*Citation.* Alexander Schrijver (2017). *A Course in Combinatorial Optimization*. URL: <https://homepages.cwi.nl/~lex/files/dict.pdf>.

*Commentary.*

Let alpha be any type in an arbitrary universe u, E a finite subset of alpha, and M1 and M2 matroids whose grounds both equal E. There are sets I and X, both contained in E, such that the same I is independent in both matroids and its cardinality equals the rank of X in M1 plus the rank of E minus X in M2. For every set J independent in both matroids and every set Y in alpha, the cardinality of J is at most the rank of Y in M1 plus the rank of E minus Y in M2.

Cardinality is Set.ncard and rank is ENat.toNat of the native Matroid.eRk. Finiteness of the common ground makes every rank finite, even when alpha is infinite. Empty grounds, loops and rank zero are included. No representation over a field or positivity assumption is required. Although the attaining X lies in E, the upper bound permits every Y; it therefore also holds for every Y contained in E.

Theorem 10.9 on page 188 of Schrijver's course states the maximum cardinality of a common independent set as the minimum of the two-rank cut sum. The finite-ground definition is on page 173. The existential equality and the universal bound exhibit both attained extrema: use the attaining cut to bound every common independent set, and use the attaining independent set to bound every cut sum from below.

The proof proceeds by induction on the ground cardinality. If every element is a loop in at least one matroid, the empty independent set and the loop set of the first matroid give equality. Otherwise a common nonloop gives smaller deletion and contraction pairs. Their two common-independent certificates combine with submodularity in each matroid; failure of attainment would force the combined cut ranks to exceed the submodular upper bound. Splitting a common independent set at an arbitrary cut gives the universal inequality.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/FiniteIntersection.finite_matroid_intersection`
