# Anholcer–Bartkowiak–Bosek–Grytczuk Conjecture 4

## Abstract

Two heterogeneous two-colorable matroids on four items admit no goods-EF1 or chores-EF1 feasible partition.

**Definition 1.1 (IsPartition).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (IsPartition\left(X\right)) \Leftrightarrow ((\forall (i: Fin\left(n\right)), \forall (j: Fin\left(n\right)), (i \ne j) \Rightarrow (Disjoint\left(X\left(i\right), X\left(j\right)\right))) \land (\forall (e: Fin\left(m\right)), \exists (i: Fin\left(n\right)), e \in X\left(i\right)))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.IsPartition` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 4: “Throughout, a partition into n bundles means an ordered n-tuple of pairwise disjoint, possibly empty, sets whose union is the relevant ground set.” Fin m enumerates the items and Fin n enumerates the agents, starting at zero. Completeness includes every item exactly once; empty bundles are allowed.

**Definition 1.2 (IndependentPartition).**

$$\forall (m: \mathbb{N}), \forall (q: \mathbb{N}), \forall (M: Matroid\left(Fin\left(m\right)\right)), \forall (X: Fin\left(q\right) \to Finset\left(Fin\left(m\right)\right)), (IndependentPartition\left(M, X\right)) \Leftrightarrow ((IsPartition\left(X\right)) \land (\forall (i: Fin\left(q\right)), \operatorname{M}.\operatorname{Indep}\left((X\left(i\right): Set\left(Fin\left(m\right)\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.IndependentPartition` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 5: “For a given independence structure M, we denote by χ(M) the chromatic number of M, that is, the least number of parts in a partition of the ground set E into independent sets.” The q bundles are independent in the same native Matroid. Each finite bundle is coerced to a Set.

**Definition 1.3 (chromaticNumber).**

$$\forall (m: \mathbb{N}), \forall (M: Matroid\left(Fin\left(m\right)\right)), chromaticNumber\left(M\right) = sInf\left(\{c: \mathbb{N}^{\infty} \mid \exists (q: \mathbb{N}), (c = (q: \mathbb{N}^{\infty})) \land (\exists (X: Fin\left(q\right) \to Finset\left(Fin\left(m\right)\right)), IndependentPartition\left(M, X\right))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.chromaticNumber` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 5: “For a given independence structure M, we denote by χ(M) the chromatic number of M, that is, the least number of parts in a partition of the ground set E into independent sets.” The infimum is in ℕ∞. An empty set of finite color counts has infimum infinity; the empty ground has color count zero. The hypotheses in claim require M.E = Set.univ.

**Definition 1.4 (Feasible).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (M: Fin\left(n\right) \to Matroid\left(Fin\left(m\right)\right)), \forall (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (Feasible\left(M, X\right)) \Leftrightarrow ((IsPartition\left(X\right)) \land (\forall (i: Fin\left(n\right)), \operatorname{Matroid}.\operatorname{Indep}\left(M\left(i\right), (X\left(i\right): Set\left(Fin\left(m\right)\right))\right)))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.Feasible` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 21: “Then there exists an EF1 partition E = X₁ ∪ ··· ∪ Xₙ such that each set Xᵢ is independent in the matroid Mᵢ, for all i = 1, 2, …, n.” Each bundle is tested in its own agent's Matroid. The ordered partition is complete.

**Definition 1.5 (value).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (w: Fin\left(n\right) \to \left(Fin\left(m\right) \to NNReal\right)), \forall (i: Fin\left(n\right)), \forall (S: Finset\left(Fin\left(m\right)\right)), value\left(w, i, S\right) = \sum_{e \in S} w\left(i, e\right)$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.value` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 4: “In this way, any subset of goods X ⊆ E, called a bundle, gets a value vᵢ(X) = ∑_{gⱼ∈X} vᵢ(gⱼ) given by agent i. Such valuations are called additive.” The singleton weights lie in NNReal, so the finite sum is nonnegative. No restriction to identical or strictly positive weights is imposed.

**Definition 1.6 (GoodsEF1).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (w: Fin\left(n\right) \to \left(Fin\left(m\right) \to NNReal\right)), \forall (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (GoodsEF1\left(w, X\right)) \Leftrightarrow (\forall (i: Fin\left(n\right)), \forall (j: Fin\left(n\right)), (X\left(j\right) = \emptyset) \lor (\exists (g: Fin\left(m\right)), (g \in X\left(j\right)) \land (value\left(w, i, \operatorname{Finset}.\operatorname{sdiff}\left(X\left(j\right), \left\{g\right\}\right)\right) \le value\left(w, i, X\left(i\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.GoodsEF1` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 4: “For general monotone valuations, we use the existential version: if Xⱼ ≠ ∅, there must exist a good g ∈ Xⱼ such that vᵢ(Xᵢ) ⩾ vᵢ(Xⱼ ∖ {g}); if Xⱼ = ∅, the condition is automatic.” This existential deletion formula also expresses additive EF1: a maximum-valued good minimizes the remaining value. The deletion is from the other agent's bundle, and the inequality compares its remaining value with the envying agent's entire bundle.

**Definition 1.7 (ChoresEF1).**

$$\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), \forall (w: Fin\left(n\right) \to \left(Fin\left(m\right) \to NNReal\right)), \forall (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (ChoresEF1\left(w, X\right)) \Leftrightarrow (\forall (i: Fin\left(n\right)), \forall (j: Fin\left(n\right)), (i \ne j) \Rightarrow ((X\left(i\right) = \emptyset) \lor (\exists (c: Fin\left(m\right)), (c \in X\left(i\right)) \land (value\left(w, i, \operatorname{Finset}.\operatorname{sdiff}\left(X\left(i\right), \left\{c\right\}\right)\right) \le value\left(w, i, X\left(j\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.ChoresEF1` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 20: “More formally, the allocation (X₁, …, Xₙ) is EF1 for chores if for every pair i ≠ j, either Xᵢ = ∅, or there exists a chore c ∈ Xᵢ such that vᵢ(Xᵢ ∖ {c}) ⩽ vᵢ(Xⱼ).” Only distinct agents are compared. Deletion is from the envying agent's own bundle.

**Definition 1.8 (claim).**

$$(claim) \Leftrightarrow (\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (M: Fin\left(n\right) \to Matroid\left(Fin\left(m\right)\right)), (\forall (i: Fin\left(n\right)), \operatorname{Matroid}.\operatorname{E}\left(M\left(i\right)\right) = \operatorname{Set}.\operatorname{univ}) \Rightarrow ((\forall (i: Fin\left(n\right)), chromaticNumber\left(M\left(i\right)\right) \le (n: \mathbb{N}^{\infty})) \Rightarrow (\forall (w: Fin\left(n\right) \to \left(Fin\left(m\right) \to NNReal\right)), (\exists (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (Feasible\left(M, X\right)) \land (GoodsEF1\left(w, X\right))) \land (\exists (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (Feasible\left(M, X\right)) \land (ChoresEF1\left(w, X\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.claim` (`✓ std3`).

*Citation.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Page 21, Conjecture 4: “Let M₁, …, Mₙ be a collection of matroids on the same ground set E satisfying χ(Mᵢ) ⩽ n, for all i = 1, 2, …, n. Suppose that there are n agents with additive valuations v₁, …, vₙ of the set of goods (or chores) E. Then there exists an EF1 partition E = X₁ ∪ ··· ∪ Xₙ such that each set Xᵢ is independent in the matroid Mᵢ, for all i = 1, 2, …, n.” The carrier is Fin m, the number n of agents is positive, every matroid has ground Set.univ, and the singleton weights are arbitrary NNReal values. The goods and chores existentials may use different allocations. This is ordinary EF1; no imaginary allocation is quantified.

**Theorem 1.9 (result).**

$$\neg (\forall (m: \mathbb{N}), \forall (n: \mathbb{N}), (0 < n) \Rightarrow (\forall (M: Fin\left(n\right) \to Matroid\left(Fin\left(m\right)\right)), (\forall (i: Fin\left(n\right)), \operatorname{Matroid}.\operatorname{E}\left(M\left(i\right)\right) = \operatorname{Set}.\operatorname{univ}) \Rightarrow ((\forall (i: Fin\left(n\right)), chromaticNumber\left(M\left(i\right)\right) \le (n: \mathbb{N}^{\infty})) \Rightarrow (\forall (w: Fin\left(n\right) \to \left(Fin\left(m\right) \to NNReal\right)), (\exists (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (Feasible\left(M, X\right)) \land (GoodsEF1\left(w, X\right))) \land (\exists (X: Fin\left(n\right) \to Finset\left(Fin\left(m\right)\right)), (Feasible\left(M, X\right)) \land (ChoresEF1\left(w, X\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-abbg2606c4` (refuted) by `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-abbg2606c4","declaration_gid":"D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marcin Anholcer; Maciej Bartkowiak; Bartłomiej Bosek; Jarosław Grytczuk (2026). *Epistemic fair division of independence structures*. URL: <https://arxiv.org/abs/2606.11494v1>.

*Commentary.*

Take four items and two agents. The first matroid has capacity-one blocks {0,1} and {2,3}; the second has blocks {1,2} and {3,0}. Both admit the two-color partition {0,2}, {1,3}. A finite certificate shows that every complete feasible allocation is one of its two orders. Both agents assign weights (3,1,3,1). The two bundle values are 6 and 2, and every deletion from the high bundle leaves 3 > 2. Thus neither order satisfies goods-EF1 or chores-EF1. The heterogeneous constraints realize a complementary-item obstruction; Dror–Feldman–Segal-Halevi, JAIR 76 (2023), Section 8.3, supplies the earlier common-nonmatroid obstruction. The common-matroid conjectures and the epistemic variants remain outside this conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.ChoresEF1`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.Feasible`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.GoodsEF1`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.IndependentPartition`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.IsPartition`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.chromaticNumber`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.result`
- Truth anchor: `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.value`
