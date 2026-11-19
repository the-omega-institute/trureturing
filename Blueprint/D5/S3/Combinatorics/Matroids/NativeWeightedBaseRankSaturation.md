# Native weighted bases and threshold-rank saturation

## Abstract

Finite native matroid minimum-weight bases are characterized by every real threshold rank.

**Definition 1.1 (The actual finite weight of a base).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (w: E \to \mathbb{R}), (\forall (B: \operatorname{Set}\left(E\right)), (\operatorname{baseWeight}\left(w, B\right) = \sum_{{e \in \operatorname{toFinite}\left(B\right).\operatorname{toFinset}}} \operatorname{w}\left(e\right))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation.baseWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite carrier, baseWeight is the finite sum of the given real weight function over the actual base set. The ground is not silently replaced by the carrier.

**Definition 1.2 (The native lower threshold set).**

$$\forall (E: Type_{u}), (\forall (M: \operatorname{Matroid}\left(E\right)), (\forall (w: E \to \mathbb{R}), (\forall (t: \mathbb{R}), (\operatorname{lowerWeightSet}\left(M, w, t\right) = \{x \mid x \in M.E \land \operatorname{w}\left(x\right) \le t\}))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation.lowerWeightSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold set retains precisely elements of the native ground M.E whose real weight is at most t.

**Theorem 1.3 (Attainment and the complete every-base threshold-rank iff).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (w: E \to \mathbb{R}), ((\exists (B: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, B\right)) \land (\forall (C: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, C\right)) \Rightarrow (\operatorname{baseWeight}\left(w, B\right) \le \operatorname{baseWeight}\left(w, C\right)))))) \land (\forall (B: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, B\right)) \Rightarrow ((\forall (C: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, C\right)) \Rightarrow (\operatorname{baseWeight}\left(w, B\right) \le \operatorname{baseWeight}\left(w, C\right)))) \Leftrightarrow (\forall (t: \mathbb{R}), (\operatorname{Set}.\operatorname{ncard}\left(\operatorname{Set}.\operatorname{inter}\left(B, \operatorname{lowerWeightSet}\left(M, w, t\right)\right)\right) = \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{Matroid}.\operatorname{eRk}\left(M, \operatorname{lowerWeightSet}\left(M, w, t\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation.native_weighted_base_rank_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite carrier E in an arbitrary universe, every native matroid M on E, and every real weight function w, a minimum-weight base exists. For each base B, minimum total weight among all bases is equivalent to saturating the native rank of every real lower threshold: the finite cardinality of B intersect {e in M.E | w(e) <= t} equals the native eRk of that set cast with toNat.

The proof uses direct finite attainment over the set of all bases. The forward direction is the native exchange argument: an unsaturated threshold admits a cheaper base exchange. The reverse direction compares sorted finite base weights from all threshold prefix inequalities, so ties, zero weights and signed weights remain in scope.

The statement includes empty carriers and grounds, rank zero, loops, coloops, proper native grounds, nonrepresentable matroids and repeated real weights. It adds no nonempty-ground, positive-rank, positivity, distinctness, supplied optimum, rank-profile or finite-state premise, and it makes no algorithmic, complexity or oracle claim.

Oki--Schwarcz, arXiv:2511.16021v3, Theorem 2.1 (https://arxiv.org/abs/2511.16021v3) gives a related rank-increment minimum-value formula. The present statement additionally characterizes every base by every real threshold and applies to native finite matroids with signed weights.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation.baseWeight`
- Truth anchor: `D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation.lowerWeightSet`
- Truth anchor: `D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation.native_weighted_base_rank_saturation`
- Dependency: [D5/S3/Estimation/ExperimentCost/MinimumCostRoleBasis](../../Estimation/ExperimentCost/MinimumCostRoleBasis.md)
