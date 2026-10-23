# Circular hypergraphs do not maximise orientation-count entropy

## Abstract

A four-edge three-uniform multihypergraph has greater entropy than the circle.

**Definition 1.1 (All cyclic paths of size r).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{circular}\left(n, r\right) = \mathit{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto Finset.image\left(\mathit{fun} (j : \mathbb{N}) \mapsto \langle\left(\operatorname{val}\left(i\right) + j\right) \bmod n\rangle, Finset.range\left(r\right)\right)$$

*Formalization.* `D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.circular` (`✓ std3`).

*Citation.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

Section 4, pp. 128–129, states: “Fix a positive integer r ≥ 3. A circular r-uniform hypergraph on n > r vertices is defined as follows: Begin with a cycle C_n on n vertices, identified with ℤ_n. A proper subset I ⊂ ℤ_n is a path in C_n if it induces a connected sub-graph of the graph C_n. The size of a path is the number of vertices in the corresponding induced sub-graph. We call a hypergraph circular if (up to isomorphism) its set of vertices is equal to ℤ_n and its edges are paths of C_n of size r. We denote by C_{n,r} the circular hypergraph on n vertices whose edge set consists of all paths of size r.” The edge at i contains the r successive vertices starting at i. The angle brackets denote the Fin n constructor; its bound proof follows from i : Fin n, which implies n>0. Finset.range r contains 0 through r−1. The modulo operation is on natural numbers. When n=0 there is no i.

**Definition 1.2 (The circular maximality conjecture).**

$$\mathit{claim} = \left(\forall r \in \mathbb{N},\; \forall n \in \mathbb{N},\; 3 \le r \Rightarrow \left(r < n \Rightarrow \left(\forall E \in \operatorname{Fin}\left(n\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; Finset.card\left(\operatorname{E}\left(i\right)\right) = r\right) \Rightarrow \operatorname{entropyX}\left(r, E\right) \le \operatorname{entropyX}\left(r, \operatorname{circular}\left(n, r\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.claim` (`✓ std3`).

*Citation.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

Section 4, p. 129, states: “We conjecture that circular hypergraphs are such that H(X_{C_{n,r}}) ≥ H(X_H), for all H ∈ D_{n,n,r}.” Here r≥3 and n>r, as in the preceding definition. Every E has n labelled edges of size r; multiplicities and isolated vertices are allowed. The functions X and entropyX are those of OrientationEntropyBalance, with the real denominator r^n and logarithm of base two. This is the maximality conjecture, distinct from the asymptotic lower bound numbered Conjecture 4.1.

**Theorem 1.3 (The circular maximality conjecture is false).**

$$\neg \mathit{claim}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.result` (`✓ std3`). ∎

*Resolves.* `Problems/pelekis-2018-circular-orientation-entropy` (refuted) by `D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pelekis-2018-circular-orientation-entropy","declaration_gid":"D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Christos Pelekis (2019). *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*. DOI: [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8). URL: <https://arxiv.org/abs/1808.04166>.

*Commentary.*

For n=4 and r=3, take {0,1,2},{0,1,2},{0,1,3},{0,1,3}. Its counts for X=0,1,2,3,4 are (0,2,27,44,8); those of circular 4 3 are (0,0,24,48,9). Both counts sum to 81. The exact comparison 2^2·27^27·44^44·8^8 < 24^24·48^48·9^9, together with H=log₂81−log₂(∏c^c)/81, proves a strict entropy advantage. Thus the circular member is not an entropy maximiser.

## References

- Truth anchor: `D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.circular`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.claim`
- Truth anchor: `D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.result`
- Dependency: [D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance](OrientationEntropyBalance.md)
