# Entropy maximisers need not have balanced degrees

## Abstract

An unbalanced three-edge multigraph maximises orientation-count entropy.

**Theorem 1.1 (Orientations as a product of finite sets).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall E \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; Finset.filter\left(\mathit{fun} (o : \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right)) \mapsto \forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{o}\left(i\right) \in \operatorname{E}\left(i\right), Finset.univ\right) = Fintype.piFinset\left(E\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.orientations_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

The functions choosing a member of every edge are exactly Fintype.piFinset E. This equality converts the orientation counts in entropyX to product-set counts.

**Theorem 1.2 (Entropy from the count product).**

$$\forall A \in \mathit{Type},\; \forall s \in \operatorname{Finset}\left(A\right),\; \forall c \in A \to \mathbb{N},\; \forall N \in \mathbb{N},\; 0 < N \Rightarrow \left(\sum_{i \in s} (\operatorname{c}\left(i\right)) = N \Rightarrow \sum_{i \in s} (-\frac{(\operatorname{c}\left(i\right) : \mathbb{R})}{(N : \mathbb{R})} \cdot Real.logb\left(2, \frac{(\operatorname{c}\left(i\right) : \mathbb{R})}{(N : \mathbb{R})}\right)) = Real.logb\left(2, (N : \mathbb{R})\right) - \frac{Real.logb\left(2, (\prod_{i \in s} (\operatorname{c}\left(i\right)^{\operatorname{c}\left(i\right)}) : \mathbb{R})\right)}{(N : \mathbb{R})}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.sum_entropy_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

For nonnegative integer counts with positive total N, the base-two entropy is log₂ N minus the logarithm of their count product divided by N. The factor for a zero count is 0^0=1. This identity compares the entropies of the three-vertex maximiser and the four-vertex circular competitor.

**Definition 1.3 (The number of vertices reached).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall E \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall o \in \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right),\; \operatorname{X}\left(E, o\right) = Finset.card\left(Finset.image\left(o, Finset.univ\right)\right)$$

*Formalization.* `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.X` (`✓ std3`).

*Citation.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

Page 122 states: “In other words, X_C is the number of vertices with non-zero in-degree after a random orientation on the edges of H_C and the above mentioned question on coloured dice can be equivalently expressed as follows.” The image of o contains exactly the vertices selected by at least one edge. E labels the edge family; the value depends only on o.

**Definition 1.4 (Shannon entropy in bits).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall E \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{entropyX}\left(r, E\right) = \sum_{k \in Finset.range\left(n + 1\right)} (\mathit{let} p := \frac{(Finset.card\left(Finset.filter\left(\mathit{fun} (o : \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right)) \mapsto \operatorname{X}\left(E, o\right) = k, Finset.filter\left(\mathit{fun} (o : \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right)) \mapsto \forall i \in \operatorname{Fin}\left(m\right),\; \operatorname{o}\left(i\right) \in \operatorname{E}\left(i\right), Finset.univ\right)\right)\right) : \mathbb{R})}{(r : \mathbb{R})^{m}}; -p \cdot Real.logb\left(2, p\right))$$

*Formalization.* `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.entropyX` (`✓ std3`).

*Citation.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

Page 120 states: “The Shannon entropy (or entropy, for short) of a random variable X that takes values on a finite set S is defined as H(X) = −∑_{s∈S} P[X = s] · log P[X = s], with the convention 0 log 0 = 0. Throughout the text, log(·) denotes logarithm with base 2.” Page 121 states: “Here and later, the phrase random orientation on the edges of a hypergraph H expresses the fact that each edge in H is oriented towards one of its elements with probability 1/r, where each edge is oriented independently of all other edges.” The two filters count orientations with X=k. Every r-uniform edge family has r^m equally likely orientations. The range includes k=0 through n; p is a real probability, so its division is real.

**Definition 1.5 (Vertex degree with edge multiplicity).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall E \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall v \in \operatorname{Fin}\left(n\right),\; \operatorname{deg}\left(E, v\right) = Finset.card\left(Finset.filter\left(\mathit{fun} (i : \operatorname{Fin}\left(m\right)) \mapsto v \in \operatorname{E}\left(i\right), Finset.univ\right)\right)$$

*Formalization.* `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.deg` (`✓ std3`).

*Citation.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

Page 122 states: “Given a hypergraph H = (V,ℰ) and a vertex v ∈ V, we denote by deg_H(v) the number of edges in ℰ that contain v.” Counting edge indices retains repeated edges.

**Definition 1.6 (Conjecture 1.3).**

$$\mathit{claim} = \left(\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; n \le m \Rightarrow \left(r < n \Rightarrow \left(2 \le r \Rightarrow \left(\forall E \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(m\right),\; Finset.card\left(\operatorname{E}\left(i\right)\right) = r\right) \Rightarrow \left(\left(\forall F \in \operatorname{Fin}\left(m\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(m\right),\; Finset.card\left(\operatorname{F}\left(i\right)\right) = r\right) \Rightarrow \operatorname{entropyX}\left(r, F\right) \le \operatorname{entropyX}\left(r, E\right)\right) \Rightarrow \left(\forall v1 \in \operatorname{Fin}\left(n\right),\; \forall v2 \in \operatorname{Fin}\left(n\right),\; (\operatorname{deg}\left(E, \mathit{v1}\right) : \mathbb{Z}) - (\operatorname{deg}\left(E, \mathit{v2}\right) : \mathbb{Z}) \le 1\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.claim` (`✓ std3`).

*Citation.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

Conjecture 1.3, p. 122, states: “Let the positive integers m,n,r be such that m ≥ n > r ≥ 2. A hypergraph H = (V,ℰ) from D_{n,m,r} for which it holds H(X_H) ≥ H(X_G), for all G ∈ D_{n,m,r} is such that |deg_H(v₁) − deg_H(v₂)| ≤ 1, for all v₁,v₂ ∈ V.” Page 121 states: “Here and later, the class consisting of all r-uniform multi-hypergraphs on n vertices and m edges is denoted by D_{n,m,r}.” Vertices are Fin n and edges are indexed by Fin m. Repeated edges and isolated vertices are allowed. The two ordered vertex choices express both signs of the absolute-value bound. The assumptions imply that n,m,r are positive.

**Theorem 1.7 (Conjecture 1.3 is false).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.result` (`✓ std3`). ∎

*Resolves.* `Problems/pelekis-2018-orientation-entropy-balance` (refuted) by `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pelekis-2018-orientation-entropy-balance","declaration_gid":"D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

Take n=m=3, r=2 and the edges {0,1},{0,1},{0,2}. The degrees are (3,2,1), and the counts for X=0,1,2,3 are (0,1,5,2) out of eight orientations. All 27 ordered edge tuples have count product ∏c^c at least 12500, equal to this example's 5^5·2^2. For a common positive denominator N and counts summing to N, entropy equals log₂ N − log₂(∏c^c)/N, with 0^0=1. Monotonicity of the logarithm therefore proves global maximality in this class, although the degrees at vertices zero and two differ by two.

## References

- Truth anchor: `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.X`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.claim`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.deg`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.entropyX`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.orientations_eq`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.result`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.sum_entropy_formula`
