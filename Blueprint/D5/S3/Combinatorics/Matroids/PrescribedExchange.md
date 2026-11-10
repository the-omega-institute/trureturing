# Rank-bounded simultaneous prescribed exchange

## Abstract

Prescriptions in opposite base differences extend to one simultaneous exchange bounded by their union rank.

**Theorem 1.1 (Prescribed exchange for arbitrary finite native matroids).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (A: \operatorname{Set}\left(E\right)), (\forall (B: \operatorname{Set}\left(E\right)), (\forall (X: \operatorname{Set}\left(E\right)), (\forall (Y: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, A\right)) \Rightarrow ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, B\right)) \Rightarrow ((X \subseteq (A \setminus B)) \Rightarrow ((Y \subseteq (B \setminus A)) \Rightarrow (\exists (U: \operatorname{Set}\left(E\right)), (\exists (V: \operatorname{Set}\left(E\right)), ((U \subseteq (A \setminus B)) \land ((V \subseteq (B \setminus A)) \land ((X \subseteq U) \land ((Y \subseteq V) \land ((\operatorname{Set}.\operatorname{ncard}\left(U\right) = \operatorname{Set}.\operatorname{ncard}\left(V\right)) \land ((\operatorname{Set}.\operatorname{ncard}\left(U\right) \le \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{Matroid}.\operatorname{eRk}\left(M, \operatorname{Set}.\operatorname{union}\left(X, Y\right)\right)\right)) \land ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, \operatorname{Set}.\operatorname{union}\left((A \setminus U), V\right)\right)) \land (\operatorname{Matroid}.\operatorname{IsBase}\left(M, \operatorname{Set}.\operatorname{union}\left((B \setminus V), U\right)\right))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrescribedExchange.exists_prescribed_exchange` (`✓ std3`). ∎

*Citation.* Taihei Oki and Tamás Schwarcz (2025). *Generalizing the Multiple Exchange Property for Matroid Bases*. URL: <https://arxiv.org/abs/2511.16021v3>.

*Commentary.*

Let E be a finite type in an arbitrary universe, M a native matroid on E, and A and B bases of M. For each prescribed subset X of A minus B and each prescribed subset Y of B minus A, one pair U,V extends both prescriptions inside the respective base differences. The two sets have equal cardinality, bounded by the native rank of X union Y. Removing U from A and adding V gives a base, and removing V from B and adding U also gives a base. Both base conclusions hold for this same pair.

Cardinality is Set.ncard and rank is ENat.toNat of Matroid.eRk. Finiteness of the ambient type makes these ranks finite. Empty carriers, proper or empty native grounds, empty prescriptions, rank zero, intersecting or coincident bases, loops, coloops and nonrepresentable matroids are included. The statement is an existence theorem and asserts no algorithmic complexity.

Contract the intersection of the bases and restrict to their union minus that intersection. The resulting bases partition the resulting native ground. Contract X and delete Y in this matroid and in its dual. The base A minus X is common to these two residual minors. Integral weight splitting for the indicator of A minus X produces a single common base C and integral summands c,d for which C is separately minimum in both minors.

For each integer threshold t, let S(t) contain residual elements with c-weight at most t, and let H(t) be the union of A intersect S(t) and B intersect S(t-1). Integrality and the indicator split identify the complement of H(t) with the d-threshold at minus t. Minimum-base threshold saturation therefore supplies both coupled rank profiles. Two applications of submodularity, together with independence inside A and B, bound the rank increase from S(t-1) to S(t) by the increase in the cardinality of B intersect C intersect S(t).

Finite lower and upper bounds on the c-weights allow the paired inequality to telescope from the empty threshold to the whole residual ground, including an empty residual ground. The resulting inequality bounds the cardinality of A intersect C plus the cardinality of X by the rank of X union Y. Take U to be the union of A intersect C with X and take V to be B minus C. The common residual base gives both exchanged bases and equal exchange cardinalities. Lifting through restriction and contraction gives both original bases; contraction rank monotonicity gives the stated bound in the original matroid.

This is the existence assertion of Oki and Schwarcz, Theorem 1.6(i). The rank argument is the paired threshold form of Section 3.1. Theorem 1.6(ii), concerning independence-oracle queries, is a separate assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PrescribedExchange.exists_prescribed_exchange`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual](../Graph/LayeredCirculation/SupplierDual.md)
- Dependency: [D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope](FiniteIntersectionPolytope.md)
- Dependency: [D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation](NativeWeightedBaseRankSaturation.md)
