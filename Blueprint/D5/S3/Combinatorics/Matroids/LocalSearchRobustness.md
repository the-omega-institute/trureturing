# Local-search robustness for finite native matroids

## Abstract

Accumulated errors of arbitrary single-exchange base paths control all nearby comparator bases.

**Definition 1.1 (An attained maximum on the actual base neighborhood).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (w: E \to \mathbb{R}), (\forall (B: \{D: \operatorname{Set}\left(E\right) \mid \operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right)\}), (\forall (t: \mathbb{N}), (\exists (A: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, A\right)) \land ((\operatorname{Set}.\operatorname{ncard}\left((A \setminus B)\right) \le t) \land ((\operatorname{baseWeight}\left(w, A\right) = \operatorname{neighborhoodMax}\left(M, w, B, t\right)) \land (\forall (D: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right)) \Rightarrow ((\operatorname{Set}.\operatorname{ncard}\left((D \setminus B)\right) \le t) \Rightarrow (\operatorname{baseWeight}\left(w, D\right) \le \operatorname{neighborhoodMax}\left(M, w, B, t\right)))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.neighborhoodMax` (`✓ std3`).

*Citation.* Taihei Oki and Tamás Schwarcz (2025). *Generalizing the Multiple Exchange Property for Matroid Bases*. URL: <https://arxiv.org/abs/2511.16021v3>.

*Commentary.*

For every universe u, finite ambient type E, native matroid M and arbitrary real weight w, W(D) is the existing NativeWeightedBaseRankSaturation.baseWeight w D. A base is represented by the subtype {D : Set E // M.IsBase D}; its set is used in all differences and weights. H_t(B) denotes neighborhoodMax M w B t. The neighborhood is exactly {D | M.IsBase D and (D minus B).ncard <= t}. It is finite because its members are subsets of the finite native ground, and nonempty because it contains B. Set.exists_max_image constructs a maximizing set, and H is the weight of that selected set. No extremum is supplied as a hypothesis.

**Definition 1.2 (The actual local error).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (w: E \to \mathbb{R}), (\forall (B0: \{D: \operatorname{Set}\left(E\right) \mid \operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right)\}), (\forall (B1: \{D: \operatorname{Set}\left(E\right) \mid \operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right)\}), (\operatorname{localError}\left(M, w, B0, B1\right) = (\operatorname{neighborhoodMax}\left(M, w, B0, 1\right) - \operatorname{baseWeight}\left(w, B1\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.localError` (`✓ std3`).

*Citation.* Taihei Oki and Tamás Schwarcz (2025). *Generalizing the Multiple Exchange Property for Matroid Bases*. URL: <https://arxiv.org/abs/2511.16021v3>.

*Commentary.*

The error is defined for two bases of the same M. A radius-one step makes the second base feasible for the first base's actual neighborhood maximum, which gives error nonnegativity.

**Theorem 1.3 (Joint-neighborhood comparison).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (w: E \to \mathbb{R}), (\forall (B0: \{D: \operatorname{Set}\left(E\right) \mid \operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right)\}), (\forall (B1: \{D: \operatorname{Set}\left(E\right) \mid \operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right)\}), (\forall (r: \mathbb{N}), ((\operatorname{Set}.\operatorname{ncard}\left((B1 \setminus B0)\right) \le 1) \Rightarrow ((\operatorname{neighborhoodMax}\left(M, w, B0, (r + 1)\right) + \operatorname{baseWeight}\left(w, B1\right)) \le (\operatorname{neighborhoodMax}\left(M, w, B1, r\right) + \operatorname{neighborhoodMax}\left(M, w, B0, 1\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.neighborhood_comparison` (`✓ std3`). ∎

*Citation.* Taihei Oki and Tamás Schwarcz (2025). *Generalizing the Multiple Exchange Property for Matroid Bases*. URL: <https://arxiv.org/abs/2511.16021v3>.

*Commentary.*

This is Oki–Schwarcz, Lemma 4.1, in the equivalent r+1 to r form for every natural r, including zero. The maximizing base A is chosen in the radius-(r+1) neighborhood of B0. The printed initial B in the source's argmax is interpreted as B0, as required by equation (21).

A base already within radius r of B1 supplies the comparison directly; A=B0 is handled separately. Coincident consecutive bases use a symmetric singleton exchange. For distinct B0,B1, write B0 minus B1={x} and B1 minus B0={y}. Membership of x,y in A gives the elementary exchange cases. In the remaining case x belongs to A and y does not, the existing PrescribedExchange.exists_prescribed_exchange is applied with X={x},Y={y}. Its rank cap gives a common exchange size of one or two.

Size two produces simultaneously a radius-r base around B1 and a radius-one base around B0, preserving the sum of weights. In size one, A minus B0 is nonempty because A and B0 are distinct bases. Select a minimum-weight element there, make a second exchange toward B1, and exchange from B0 toward A. The minimum-weight inequality compensates the weight difference, and both required radii hold for this same pair of bases.

**Theorem 1.4 (Every error is nonnegative and every radius-k comparator is controlled).**

$$\forall (E: Type_{u}), ([\operatorname{Finite}\left(E\right)], \forall (M: \operatorname{Matroid}\left(E\right)), (\forall (w: E \to \mathbb{R}), (\forall (k: \mathbb{N}), (\forall (B: \operatorname{Fin}\left((k + 1)\right) \to \{D: \operatorname{Set}\left(E\right) \mid \operatorname{Matroid}.\operatorname{IsBase}\left(M, D\right)\}), ((\forall (i: \operatorname{Fin}\left(k\right)), (\operatorname{Set}.\operatorname{ncard}\left((\operatorname{B}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right) \setminus \operatorname{B}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right))\right) \le 1)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(k\right)), (0 \le \operatorname{localError}\left(M, w, \operatorname{B}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), \operatorname{B}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\right))) \land (\forall (C: \operatorname{Set}\left(E\right)), ((\operatorname{Matroid}.\operatorname{IsBase}\left(M, C\right)) \Rightarrow ((\operatorname{Set}.\operatorname{ncard}\left((C \setminus \operatorname{B}\left(0\right))\right) \le k) \Rightarrow (\operatorname{baseWeight}\left(w, C\right) \le (\operatorname{baseWeight}\left(w, \operatorname{B}\left(\operatorname{Fin}.\operatorname{last}\left(k\right)\right)\right) + \sum_{{i: \operatorname{Fin}\left(k\right)}} \operatorname{localError}\left(M, w, \operatorname{B}\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), \operatorname{B}\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.local_search_robustness` (`✓ std3`). ∎

*Citation.* Taihei Oki and Tamás Schwarcz (2025). *Generalizing the Multiple Exchange Property for Matroid Bases*. URL: <https://arxiv.org/abs/2511.16021v3>.

*Commentary.*

The finite path B : Fin(k+1) -> Base(M) consists of bases of one and the same native matroid. For i : Fin k, i.castSucc indexes Bi and i.succ indexes B(i+1). The sum is over every i : Fin k, and Fin.last k indexes Bk. The conclusion includes every base C in the actual radius-k neighborhood of B0; it is not a claim about a selected comparator alone.

Repeated application of the joint comparison gives H_k(B0) <= H_(k-1)(B1)+err_0 <= ... <= H_0(Bk)+sum_i err_i. The induction implements this telescope on the finite path and proves H_0(Bk)=W(Bk), since a base contained in another base equals it. The actual neighborhood maximum bounds each feasible comparator.

This is the mathematical assertion of Oki–Schwarcz, Theorem 1.7, Section 4, printed pages 19–20. The scope retains k=0, repeated bases, signed weights, empty carrier or ground, proper grounds, rank zero, loops, coloops and nonrepresentable matroids. There is no strict-improvement, optimal-start, distinct-step or representability premise, and no supplied maximum, error or optimality premise. The theorem makes no claim about algorithms, query counts, complexity or physical models.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.localError`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.local_search_robustness`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.neighborhoodMax`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LocalSearchRobustness.neighborhood_comparison`
- Dependency: [D5/S3/Combinatorics/Matroids/PrescribedExchange](PrescribedExchange.md)
