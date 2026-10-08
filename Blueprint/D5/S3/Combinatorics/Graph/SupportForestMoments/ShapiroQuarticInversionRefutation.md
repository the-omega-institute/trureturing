# The unweighted fourth moment does not determine four-edge forest counts

## Abstract

Two trees have equal Laplacian characteristic polynomials, lower support counts and moments through degree four, but different four-edge path counts.

**Definition 1.1 (Shapiro's inversion question).**

$$claim \Leftrightarrow (\forall (n : \mathbb{N}), (4 \le n) \Rightarrow (\forall (T : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (Tprime : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{SimpleGraph.IsTree}\left(T\right)) \Rightarrow ((\operatorname{SimpleGraph.IsTree}\left(Tprime\right)) \Rightarrow ((\operatorname{Matrix.charpoly}\left(\operatorname{SimpleGraph.lapMatrix}\left(T, \mathbb{Z}\right)\right) = \operatorname{Matrix.charpoly}\left(\operatorname{SimpleGraph.lapMatrix}\left(Tprime, \mathbb{Z}\right)\right)) \Rightarrow ((\forall (h : \mathbb{N}), \forall (F : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(h\right)\right)), (noIsolated\left(F\right)) \Rightarrow ((\operatorname{SimpleGraph.IsAcyclic}\left(F\right)) \Rightarrow ((\operatorname{Finset.card}\left(\operatorname{SimpleGraph.edgeFinset}\left(F\right)\right) \le 3) \Rightarrow (N_{H}\left(T, F\right) = N_{H}\left(Tprime, F\right))))) \Rightarrow ((\forall (r : \mathbb{N}), (r \in (\{2, 3, 4\} : \operatorname{Finset}\left(\mathbb{N}\right))) \Rightarrow (M_{r2}\left(T, r\right) = M_{r2}\left(Tprime, r\right))) \Rightarrow (\forall (h : \mathbb{N}), \forall (F : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(h\right)\right)), (noIsolated\left(F\right)) \Rightarrow ((\operatorname{SimpleGraph.IsAcyclic}\left(F\right)) \Rightarrow ((\operatorname{Finset.card}\left(\operatorname{SimpleGraph.edgeFinset}\left(F\right)\right) = 4) \Rightarrow (N_{H}\left(T, F\right) = N_{H}\left(Tprime, F\right)))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.claim` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

Section 12, page 13, Outlook item 1: "Compute an explicit closed formula for the unweighted fourth moment and invert it, modulo Laplacian and cubic data, on the finite list of four-edge support forests. The degree-three inversion is complete by the cubic inversion theorem above." The inversion implication quantifies over n ≥ 4, all trees on Fin n, every forest without isolated vertices with at most three edges, and every such forest with exactly four edges. Laplacian data is the characteristic polynomial over ℤ. The moments use the right side of (6.2); the integer r ranges over {2,3,4}. A refutation answers the inversion part; it makes no claim that a closed fourth-moment formula does not exist.

**Definition 1.2 (Edges of the first tree).**

$$EA = \{s\left(0, 5\right), s\left(0, 10\right), s\left(0, 11\right), s\left(0, 1\right), s\left(1, 2\right), s\left(2, 3\right), s\left(3, 4\right), s\left(5, 6\right), s\left(5, 9\right), s\left(6, 7\right), s\left(6, 8\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.EA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These eleven unordered pairs lie in Sym2 (Fin 12). Labels are 0 through 11.

**Definition 1.3 (First tree).**

$$A = \operatorname{SimpleGraph.fromEdgeSet}\left((EA : \operatorname{Set}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(12\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph has exactly the displayed edges. Its paths from vertex zero establish connectedness; eleven edges on twelve vertices give the tree property.

**Definition 1.4 (Edges of the second tree).**

$$EB = \{s\left(0, 8\right), s\left(0, 1\right), s\left(1, 2\right), s\left(1, 5\right), s\left(1, 7\right), s\left(2, 3\right), s\left(2, 4\right), s\left(5, 6\right), s\left(8, 9\right), s\left(9, 10\right), s\left(9, 11\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.EB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These eleven unordered pairs lie in Sym2 (Fin 12).

**Definition 1.5 (Second tree).**

$$B = \operatorname{SimpleGraph.fromEdgeSet}\left((EB : \operatorname{Set}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(12\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph has exactly the displayed edges and is also a tree.

**Definition 1.6 (Four-edge path).**

$$P5 = \operatorname{SimpleGraph.fromEdgeSet}\left(((\{s\left(0, 1\right), s\left(1, 2\right), s\left(2, 3\right), s\left(3, 4\right)\} : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(5\right)\right)\right)) : \operatorname{Set}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(5\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.P5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source's path model has five vertices and four edges. It has no isolated vertex and is acyclic.

**Theorem 1.7 (Fourth moment of the first tree).**

$$M_{r2}\left(A, 4\right) = 234836$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.A_M4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursive evaluator splits the first two choices, evaluates all remaining ordered edge pairs, and sums the resulting eleven-by-eleven integer table. Its soundness theorem identifies this value with the literal edge-word moment. This equality is used in comparing the two trees' moments.

**Theorem 1.8 (Failure of quartic inversion).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/shapiro-2026-unweighted-fourth-moment-inversion` (refuted) by `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shapiro-2026-unweighted-fourth-moment-inversion","declaration_gid":"D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

The twelve-vertex pair A, B has the same Laplacian characteristic polynomial, as certified by a rational invertible intertwiner. Explicit bijections between their edge subsets match every support of size at most three. The edge-word sums give M₂ = 3164, M₃ = 26730 and M₄ = 234836 for both trees. Their P5 support counts are respectively 12 and 10, contradicting the inversion implication. This is a statement about the base pair. It does not establish an infinite family or equality of the full (n−2,2)-spectrum, and it does not refute either conjecture using all moments.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.A`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.A_M4`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.B`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.EA`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.EB`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.P5`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroQuarticInversionRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection](SupportAndEdgeWordReflection.md)
