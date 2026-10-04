# The independence Morse ensemble does not determine the chromatic polynomial

## Abstract

Two graphs on eight vertices have identical independence Morse ensembles and different numbers of proper four-colourings. Thus the chromatic polynomial is not a function of the independence Morse ensemble.

**Definition 1.1 (The nonempty independence complex).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \operatorname{independenceComplex}\left(G\right) = \operatorname{filter}\left(\operatorname{univ}, (s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{Nonempty}\left(s\right)) \land (\operatorname{IsIndepSet}\left(G, (\operatorname{coe}\left(s\right): \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.independenceComplex` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Definition 6.1 (p. 24): "For a graph G = (V, E), the independence complex Ind(G) = {I ⊆ V | I independent in G} is a simplicial complex of dimension α(G)−1, where α(G) is the independence number, the size of the largest independent set." The vertices are Fin n. Only nonempty independent sets are faces; the empty set is excluded from the face poset, as in the dimension-indexed Morse vector. IsIndepSet is Mathlib's predicate, and the coercion in the formula is from a finite set to a set of vertices.

**Definition 1.2 (Covering pairs).**

$$\forall (n: \mathbb{N}), \forall (F: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)), \operatorname{coveringPairs}\left(F\right) = \operatorname{filter}\left(\operatorname{product}\left(F, F\right), (p: (\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \times \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))) \mapsto (p_{1} \subset p_{2}) \land (\operatorname{card}\left(p_{2}\right) = \operatorname{card}\left(p_{1}\right) + 1)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.coveringPairs` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Section 2 (pp. 3–4): "The face poset P(K) of a finite simplicial complex K is the partially ordered set of all simplices of K, ordered by inclusion. Its covering relations are precisely the pairs σ ≺ τ with σ ⊂ τ and dim τ = dim σ + 1." Face cardinality is dimension plus one. The product is the Cartesian product of finite sets.

**Definition 1.3 (Disjoint endpoint faces).**

$$\forall (A: \operatorname{Type}), [\operatorname{DecidableEq}\left(A\right)], \forall (p: A \times A), \forall (q: A \times A), (\operatorname{Compatible}\left(p, q\right)) \Leftrightarrow ((p_{1} \ne q_{1}) \land ((p_{1} \ne q_{2}) \land ((p_{2} \ne q_{1}) \land (p_{2} \ne q_{2}))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Compatible` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Two distinct covering pairs can belong to the same matching exactly when their endpoint faces are all different. The four inequalities compare the first and second coordinates of the two pairs.

**Definition 1.4 (A finite topological ranking).**

$$\forall (A: \operatorname{Type}), \forall (S: \operatorname{Finset}\left(A\right)), \forall (R: A \to A \to \operatorname{Prop}), (\operatorname{Acyclic}\left(S, R\right)) \Leftrightarrow (\exists (rank: A \to \mathbb{N}), \forall a \in S, \forall b \in S, (R\left(a, b\right)) \Rightarrow (rank\left(a\right) < rank\left(b\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Acyclic` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

A natural-valued rank strictly increases along every arrow whose endpoints lie in S. On a finite set this is equivalent to absence of a nonempty directed cycle. The rank is a certificate, and different ranks for the same matching are not counted as different matchings.

**Definition 1.5 (All acyclic matchings, each once).**

$$\forall (A: \operatorname{Type}), [\operatorname{DecidableEq}\left(A\right)], \forall (F: \operatorname{Finset}\left(A\right)), \forall (C: \operatorname{Finset}\left((A \times A)\right)), \operatorname{acyclicMatchings}\left(F, C\right) = \operatorname{filter}\left(\operatorname{powerset}\left(C\right), (M: \operatorname{Finset}\left((A \times A)\right)) \mapsto (\forall p \in M, \forall q \in M, (p \ne q) \Rightarrow (\operatorname{Compatible}\left(p, q\right))) \land (\operatorname{Acyclic}\left(F, (a: A) \mapsto (b: A) \mapsto ((a, b) \in M) \lor (((b, a) \in C) \land (\neg ((b, a) \in M)))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.acyclicMatchings` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Section 2 (p. 4): "An acyclic matching on P(K) is a collection M of covering pairs (σ, τ) such that each simplex of K appears in at most one pair and such that the Hasse diagram, after reversing the matched edges, contains no directed cycle [12]." The powerset lists subsets of C exactly once. The filter imposes the four endpoint inequalities and the strictly increasing ranking condition. In the independence complex, C is coveringPairs F. The displayed arrow relation points upward on matched pairs and downward on the remaining pairs. Certificates distinguish acyclic and cyclic candidates, but the coefficients count matchings, not certificates.

**Definition 1.6 (Critical faces).**

$$\forall (n: \mathbb{N}), \forall (M: \operatorname{Finset}\left((\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \times \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)), \forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Critical}\left(M, s\right)) \Leftrightarrow (\forall p \in M, (s \ne p_{1}) \land (s \ne p_{2}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Critical` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Section 2 (p. 4): "The simplices not appearing in any pair of M are called critical. We write c_i(M) for the number of critical i-simplices." A face is critical if it is unequal to either coordinate of every matching pair.

**Definition 1.7 (Largest face cardinality).**

$$\forall (n: \mathbb{N}), \forall (F: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)), \operatorname{alpha}\left(F\right) = \operatorname{sup}\left(F, \operatorname{card}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.alpha` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

The maximum face cardinality is the supremum of card over the finite set F, with value zero for the empty complex. For the independence complex this is α(G), the independence number.

**Definition 1.8 (Critical simplices in each dimension).**

$$\forall (n: \mathbb{N}), \forall (F: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (M: \operatorname{Finset}\left((\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \times \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)), \forall (i: \mathbb{N}), \operatorname{criticalCount}\left(F, M, i\right) = \operatorname{card}\left(\operatorname{filter}\left(F, (s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{card}\left(s\right) = i + 1) \land (\operatorname{Critical}\left(M, s\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.criticalCount` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Critical i-simplices have cardinality i+1. Each face is counted once, without quotienting by graph automorphisms.

**Definition 1.9 (The whole Morse vector).**

$$\forall (n: \mathbb{N}), \forall (F: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (M: \operatorname{Finset}\left((\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \times \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)), \operatorname{morseVector}\left(F, M\right) = \operatorname{map}\left(\operatorname{criticalCount}\left(F, M\right), \operatorname{range}\left(\operatorname{alpha}\left(F\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.morseVector` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

The list contains the critical counts in dimensions 0 through alpha F minus one, in this order. Its length is alpha F, and an empty complex has the empty vector. Lists provide a common carrier for graphs with different numbers of vertices.

**Definition 1.10 (Morse-vector multiplicities).**

$$\forall (n: \mathbb{N}), \forall (F: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (C: \operatorname{Finset}\left((\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \times \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)), \operatorname{ensemble}\left(F, C\right) = \sum_{M \in \operatorname{acyclicMatchings}\left(F, C\right)} \operatorname{single}\left(\operatorname{morseVector}\left(F, M\right), 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.ensemble` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Definition 1.1 (p. 2): "The Morse ensemble polynomial of K is" ME_K(z_0, …, z_d) = Σ_{M ∈ A(K)} Π_{i=0}^{d} z_i^{c_i(M)}, "where A(K) denotes the set of all acyclic matchings on P(K)." The finitely supported natural-valued function ensemble records precisely each entire exponent vector's coefficient: single(v,1) contributes one at v and zero elsewhere. The formula displays its defining sum, not an evaluation at particular values of the polynomial variables.

**Definition 1.11 (The independence Morse ensemble).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \operatorname{Phi}\left(G\right) = \operatorname{ensemble}\left(\operatorname{independenceComplex}\left(G\right), \operatorname{coveringPairs}\left(\operatorname{independenceComplex}\left(G\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Phi` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Definition 6.1 (p. 24): "We define the independence ME polynomial" Φ(G) := ME_{Ind(G)}(z_0, z_1, …, z_{α(G)−1}), "the Morse ensemble polynomial of the independence complex of G." Phi is its complete Morse-vector coefficient data. The nonempty independence complex supplies the faces and covering pairs.

**Definition 1.12 (Proper colourings with labelled colours).**

$$\forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (k: \mathbb{N}), \operatorname{chromaticCount}\left(G, k\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}, (c: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(k\right)) \mapsto \forall (a: \operatorname{Fin}\left(n\right)), \forall (b: \operatorname{Fin}\left(n\right)), (\operatorname{Adj}\left(G, a, b\right)) \Rightarrow (c\left(a\right) \ne c\left(b\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.chromaticCount` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

chromaticCount G k is χ(G; k), the number of functions Fin n → Fin k assigning unequal colours to adjacent vertices. Colours are labelled, and colour permutations are not quotiented out. The edge condition is Mathlib's Coloring condition; positivity is equivalent to G.Colorable k.

**Definition 1.13 (Zheng's recovery question).**

$$(claim) \Leftrightarrow (\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(m\right)\right)), (\operatorname{Phi}\left(G\right) = \operatorname{Phi}\left(H\right)) \Rightarrow (\forall (k: \mathbb{N}), \operatorname{chromaticCount}\left(G, k\right) = \operatorname{chromaticCount}\left(H, k\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.claim` (`✓ std3`).

*Citation.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Open problem (4), p. 29: "Recovery from Φ(G). Theorem 6.4 shows that Φ(G) determines ME_G, and hence the Laplacian spectrum of G. Which further graph parameters are functions of Φ(G)? For instance, is the chromatic polynomial χ(G; t) always recoverable from Φ(G)?" The quantified assertion says that any two finite simple graphs with equal entire Phi data have equal proper-colouring counts at every natural k. Equality of chromatic polynomials implies these equalities, so a counterexample at k=4 answers the printed question negatively. The quantification includes arbitrary n and m, including the empty graph.

**Theorem 1.14 (A negative answer).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zheng-2026-morse-ensemble-chromatic-recovery-refutation` (refuted) by `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zheng-2026-morse-ensemble-chromatic-recovery-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chong Zheng (2026). *On the Morse Ensemble Polynomial of Simplicial Complexes*. DOI: [10.48550/arXiv.2605.24689](https://doi.org/10.48550/arXiv.2605.24689). URL: <https://arxiv.org/abs/2605.24689v3>.

*Commentary.*

Let Hone have edges 01, 07, 12, 23, 27, 34, 47, 56, and Htwo have edges 03, 04, 12, 17, 25, 26, 57, 67, on vertices 0 through 7. Take their complements Gone and Gtwo. Their nonempty independence complexes consist of the eight vertices and eight edges of Hone and Htwo. Each has acyclic-matching size counts [1,16,102,332,581,516,180,0,0]; a matching of size r has Morse vector [8−r,8−r], so Phi Gone = Phi Gtwo. The colouring [0,0,1,1,2,3,3,2] proves Gone is four-colourable. The vertices {1,3,4,5,6} form a five-clique in Gtwo, so chromaticCount Gtwo 4 = 0. Thus the common Phi does not determine the chromatic polynomial. Private certificate lists assign a natural-valued rank or directed cycle to each candidate; every code is checked against its matching, and exhaustive enumeration and uniqueness are proved. The count 72 and the full chromatic polynomials are not asserted by this theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Acyclic`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Compatible`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Critical`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.Phi`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.acyclicMatchings`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.alpha`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.chromaticCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.coveringPairs`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.criticalCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.ensemble`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.independenceComplex`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.morseVector`
- Truth anchor: `D5/S3/Combinatorics/Graph/MorseEnsembleChromaticRefutation.result`
