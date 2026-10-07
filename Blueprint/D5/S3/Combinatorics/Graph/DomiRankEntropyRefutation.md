# Increasing DomiRank entropy on connected nonregular graphs

## Abstract

DomiRank entropy can increase with competition on a connected nonregular simple graph. A six-vertex graph gives an exact entropy gap and a whole increasing interval; independent clones give the same behavior on 6m vertices for every positive integer m.

**Definition 1.1 (Unequal degrees).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], [\operatorname{DecidableEq}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(W\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], (\operatorname{Nonregular}\left(G\right)) \Leftrightarrow (\exists (u : W) (v : W), \sum_{w} \operatorname{ite}\left(\operatorname{Adj}\left(G, u, w\right), 1, 0\right) \ne \sum_{w} \operatorname{ite}\left(\operatorname{Adj}\left(G, v, w\right), 1, 0\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.Nonregular` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

Nonregular means that two vertices have different degrees. The finite sum counts the neighbors of each vertex.

**Definition 1.2 (Positive scores).**

$$\forall (W : Type), \forall (p : W \to \mathbb{R}), \forall (i : W), \operatorname{clipped}\left(p, i\right) = \operatorname{max}\left(\operatorname{p}\left(i\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.clipped` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

Negative scores are replaced by zero. This is the positive-part convention used for the entropy distribution.

**Definition 1.3 (Normalizing the positive part).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], \forall (p : W \to \mathbb{R}), \forall (i : W), \operatorname{normalized}\left(p, i\right) = \frac{\operatorname{clipped}\left(p, i\right)}{\sum_{j} \operatorname{clipped}\left(p, j\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.normalized` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

The positive scores are divided by their total mass. Real division gives a total definition, including when the denominator is zero. For connected nonregular graphs at stable positive parameters the proof establishes invertibility of I+sA, the equilibrium equation and strictly positive clipped mass; the claim requires no additional normalizer premise.

**Definition 1.4 (Shannon entropy in bits).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], \forall (p : W \to \mathbb{R}), \operatorname{entropyBits}\left(p\right) = \frac{\operatorname{shannonEntropy}\left(p\right)}{\operatorname{log}\left(2\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.entropyBits` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

The finite Shannon entropy is the negative sum of p_i log(p_i), with the natural logarithm and the usual zero contribution at p_i=0. Division by log(2) converts it to bits. shannonEntropy is the existing finite entropy definition.

**Definition 1.5 (The least adjacency eigenvalue).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(W\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \operatorname{spectralMinimum}\left(G\right) = \left\{\begin{aligned}\operatorname{infPrime}\left(\operatorname{univ}\left(W\right), \operatorname{eigenvalues}\left(\operatorname{isHermitianAdjMatrix}\left(G, \mathbb{R}\right)\right)\right) & \text{if} \operatorname{Nonempty}\left(W\right)\\0 & \text{otherwise}\end{aligned}\right.$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.spectralMinimum` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

The real adjacency matrix is Hermitian. On a nonempty finite vertex type, spectralMinimum is the minimum of its real eigenvalues; infPrime denotes Finset.inf' over all indices. The empty type is assigned zero. The claim has n>0, and its stable domain is 0<s<-1/spectralMinimum(G).

**Definition 1.6 (The actual adjacency matrix).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(W\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \operatorname{graphAdj}\left(G\right) = \operatorname{adjMatrix}\left(G, \mathbb{R}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphAdj` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

graphAdj is Mathlib's real adjacency matrix of the given simple graph, with entries one on edges and zero elsewhere.

**Definition 1.7 (The degree vector).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(W\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \operatorname{graphDegrees}\left(G\right) = \operatorname{mulVec}\left(\operatorname{graphAdj}\left(G\right), (i \mapsto 1)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphDegrees` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

Multiplying adjacency by the all-ones vector gives the actual degree vector.

**Definition 1.8 (The inverse equilibrium).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], [\operatorname{DecidableEq}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(W\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (s : \mathbb{R}), \operatorname{graphGamma}\left(G, s\right) = s \cdot \operatorname{mulVec}\left((1 + s \cdot \operatorname{graphAdj}\left(G\right))^{-1}, \operatorname{graphDegrees}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphGamma` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

The source equilibrium uses theta=1 and sigma=s. The inverse is Mathlib's nonsingular matrix inverse. On the stable spectral domain I+sA is invertible, so this definition satisfies the actual equilibrium equation. No scalar proxy replaces the adjacency or inverse.

**Definition 1.9 (Entropy of the equilibrium).**

$$\forall (W : Type), [\operatorname{Fintype}\left(W\right)], [\operatorname{DecidableEq}\left(W\right)], \forall (G : \operatorname{SimpleGraph}\left(W\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (s : \mathbb{R}), \operatorname{graphEntropyBits}\left(G, s\right) = \operatorname{entropyBits}\left(\operatorname{normalized}\left(\operatorname{graphGamma}\left(G, s\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphEntropyBits` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

The inverse equilibrium is positively clipped and normalized before taking Shannon entropy in bits.

**Definition 1.10 (The unconditional question in Remark 4.6).**

$$(claim) \Leftrightarrow (\forall (n : \mathbb{N}), (0 < n) \Rightarrow (\forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], (\operatorname{Connected}\left(G\right)) \Rightarrow ((\operatorname{Nonregular}\left(G\right)) \Rightarrow (\forall (sigma : \mathbb{R}), \forall (tau : \mathbb{R}), ((0 < sigma) \land (sigma < \frac{-1}{\operatorname{spectralMinimum}\left(G\right)})) \Rightarrow (((0 < tau) \land (tau < \frac{-1}{\operatorname{spectralMinimum}\left(G\right)})) \Rightarrow ((sigma < tau) \Rightarrow (\operatorname{graphEntropyBits}\left(G, tau\right) \le \operatorname{graphEntropyBits}\left(G, sigma\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.claim` (`✓ std3`).

*Citation.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

Remark 4.6 asks whether the DomiRank entropy of a connected non-regular graph decreases monotonically with sigma. claim expresses nonincrease for every finite connected nonregular simple graph and every ordered pair of positive parameters in the full stable spectral domain. Fin(n) labels the vertices without restricting finite graph isomorphism classes. The conditional Theorem 4.5 and the star-minimum Conjecture 4.7 are separate statements.

**Theorem 1.11 (An exact pair, a whole interval, and independent clones).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-zhao-2026-domirank-entropy-monotonicity` (refuted) by `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-zhao-2026-domirank-entropy-monotonicity","declaration_gid":"D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yingying Zhang and Chengye Zhao (2026). *Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations*. DOI: [10.48550/arXiv.2610.00107](https://doi.org/10.48550/arXiv.2610.00107). URL: <https://arxiv.org/abs/2610.00107v1>.

*Commentary.*

Take vertices 0 through 5 and edges {0,4}, {0,5}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4}. This graph is connected, has degree vector (2,3,3,2,3,1), and has least eigenvalue in [-3,-1]. Its actual equilibrium vectors at 1/20 and 1/6 are (397,577,577,378,576,198)/4357 and (33,45,45,28,44,16)/129. Their coordinates are strictly between zero and one. Rational logarithm bounds with integral remainders give H(1/6)-H(1/20)>1/(500 log(2)).

For every finite nonempty graph with positive degrees d, put D=sum_i d_i, w_i=d_i/D and q_i=(Ad)_i/d_i. The derivative at zero of the normalized inverse extension is (sum_i w_i q_i log(d_i) - (sum_i w_i q_i)(sum_i w_i log(d_i)))/log(2). For this graph it equals log(27/2)/(49 log(2))>0. Explicit derivative bounds give H(a)<H(b) for every 0<a<b<delta, delta=1/5000000, with admissible parameters and scores strictly between zero and one. Zero is only a point of the normalized inverse extension; clipped Gamma at zero does not give that extension and zero is never a source-domain point.

For every natural m>0, replace each vertex by m independent clones and every edge by all edges between its clone classes. On Fin(6) x Fin(m) the actual adjacency depends only on the first coordinates. The graph is connected and nonregular, has 6m vertices and least eigenvalue in [-3m,-m]. For 0<s<1/(3m), the inverse equilibrium replicates Gamma_G(ms), the probabilities satisfy P_m(s)_(i,j)=P_G(ms)_i/m, and H_m(s)=H_G(ms)+log(m)/log(2). Thus the pair 1/(20m),1/(6m) has the same strict entropy gap, and every 0<a<b<delta/m has admissible parameters, positive scores below one, and H_m(a)<H_m(b).

These covariance, interval and clone identities are local to result. The family at m=1 transfers both the exact-pair increment and an interval increment back to the base graph. Their sum is strictly positive, whereas claim would make both increments nonpositive. This proves the negation of the universal source assertion. The reduced cubic coordinate denominator is not asserted to be the adjacency determinant.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.Nonregular`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.clipped`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.entropyBits`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphDegrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphEntropyBits`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.graphGamma`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.normalized`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.spectralMinimum`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../Entropy/MaxEntropy.md)
