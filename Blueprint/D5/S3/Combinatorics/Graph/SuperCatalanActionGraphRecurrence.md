# Super Catalan numbers from action-graph path tables

## Abstract

For every nonnegative n, the weighted sum of the path-table columns of the recursively constructed action graph equals S(0, n + 1).

**Definition 1.1 (Labeled rooted trees).**

$$\begin{aligned}\operatorname{Tree}:\operatorname{Type}\\\operatorname{Tree}.\operatorname{node}:\mathbb{N} \to \left(\operatorname{List}\left(\operatorname{Tree}\right) \to \operatorname{Tree}\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.Tree` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 15: “Definition 5.2. We construct the sequence generalized action graphs, denoted {Gn}, for the super Catalan numbers as sequence of directed graphs defined inductively in the following way. The graph G0 is a single vertex labeled 0. To construct Gn+1 from Gn, consider each vertex v in Gn. For each 0 ≤ ℓ ≤ n, add p(v, ℓ) · 2/2^ℓ new vertices labeled n + 1 with edges from v, where p(v, ℓ) is the number of paths of length ℓ from v to vertices labeled n in Gn.” Each new vertex has exactly one parent. Tree.node records its label and its list of children; repeated list entries represent distinct vertices, with all edges directed from parent to child.

**Definition 1.2 (Paths from a root).**

$$\begin{aligned}\forall a \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall cs \in \operatorname{List}\left(\operatorname{Tree}\right),\; \operatorname{paths}\left(\operatorname{Tree}.\operatorname{node}\left(a, cs\right), 0, k\right) = \operatorname{if} a = k \operatorname{then} 1 \operatorname{else} 0\\\forall a \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall cs \in \operatorname{List}\left(\operatorname{Tree}\right),\; \operatorname{paths}\left(\operatorname{Tree}.\operatorname{node}\left(a, cs\right), r + 1, k\right) = \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{fun} (c:\operatorname{Tree}) \mapsto \operatorname{paths}\left(c, r, k\right), cs\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.paths` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 15: “Definition 5.2. We construct the sequence generalized action graphs, denoted {Gn}, for the super Catalan numbers as sequence of directed graphs defined inductively in the following way. The graph G0 is a single vertex labeled 0. To construct Gn+1 from Gn, consider each vertex v in Gn. For each 0 ≤ ℓ ≤ n, add p(v, ℓ) · 2/2^ℓ new vertices labeled n + 1 with edges from v, where p(v, ℓ) is the number of paths of length ℓ from v to vertices labeled n in Gn.” paths(t, r, k) is the source's p(v, ℓ), with r = ℓ and t the subtree rooted at v. The zero-length path starts and ends at the root. Paths of positive length first choose one child and then follow a shorter path.

**Definition 1.3 (Adding the next generation).**

$$\forall n \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall cs \in \operatorname{List}\left(\operatorname{Tree}\right),\; \operatorname{grow}\left(n, \operatorname{Tree}.\operatorname{node}\left(a, cs\right)\right) = \operatorname{Tree}.\operatorname{node}\left(a, \operatorname{List}.\operatorname{map}\left(\operatorname{grow}\left(n\right), cs\right) ++ \operatorname{List}.\operatorname{replicate}\left(\sum_{r \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (\operatorname{Nat}.\operatorname{div}\left(\operatorname{paths}\left(\operatorname{Tree}.\operatorname{node}\left(a, cs\right), r, n\right) \cdot 2, 2^{r}\right)), \operatorname{Tree}.\operatorname{node}\left(n + 1, []\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.grow` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 15: “Definition 5.2. We construct the sequence generalized action graphs, denoted {Gn}, for the super Catalan numbers as sequence of directed graphs defined inductively in the following way. The graph G0 is a single vertex labeled 0. To construct Gn+1 from Gn, consider each vertex v in Gn. For each 0 ≤ ℓ ≤ n, add p(v, ℓ) · 2/2^ℓ new vertices labeled n + 1 with edges from v, where p(v, ℓ) is the number of paths of length ℓ from v to vertices labeled n in Gn.” All path counts are taken in the old tree. Nat.div denotes natural-number quotient, including its total convention at zero; the denominators here are powers of two and are nonzero. The divisibility invariant proves that these quotients are exact for every subtree of G(n). The append operator ++ and List.replicate retain vertex multiplicities.

**Definition 1.4 (The graph sequence).**

$$\begin{aligned}\operatorname{G}\left(0\right) = \operatorname{Tree}.\operatorname{node}\left(0, []\right)\\\forall n \in \mathbb{N},\; \operatorname{G}\left(n + 1\right) = \operatorname{grow}\left(n, \operatorname{G}\left(n\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.G` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 15: “Definition 5.2. We construct the sequence generalized action graphs, denoted {Gn}, for the super Catalan numbers as sequence of directed graphs defined inductively in the following way. The graph G0 is a single vertex labeled 0. To construct Gn+1 from Gn, consider each vertex v in Gn. For each 0 ≤ ℓ ≤ n, add p(v, ℓ) · 2/2^ℓ new vertices labeled n + 1 with edges from v, where p(v, ℓ) is the number of paths of length ℓ from v to vertices labeled n in Gn.” The initial tree is one vertex labeled zero, and the next graph is obtained by applying grow to the whole old graph.

**Definition 1.5 (Paths from every vertex of a label).**

$$\forall a \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall v \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall cs \in \operatorname{List}\left(\operatorname{Tree}\right),\; \operatorname{pathsFrom}\left(\operatorname{Tree}.\operatorname{node}\left(a, cs\right), r, v, k\right) = (\operatorname{if} a = v \operatorname{then} \operatorname{paths}\left(\operatorname{Tree}.\operatorname{node}\left(a, cs\right), r, k\right) \operatorname{else} 0) + \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left(\operatorname{fun} (c:\operatorname{Tree}) \mapsto \operatorname{pathsFrom}\left(c, r, v, k\right), cs\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.pathsFrom` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 16: “Definition 5.4. Let Kℓ,v,n be the number of paths of length ℓ in Gn that start at a vertex labeled v and end at a vertex labeled n. For a given n, the table of Kℓ,v,n for all values of ℓ and v is called the n-table.” pathsFrom(t, r, v, k) sums over every starting vertex labeled v in t. Its root contribution is included exactly when the root label equals v; recursive child contributions include every other vertex once.

**Definition 1.6 (The n-table).**

$$\forall r \in \mathbb{N},\; \forall v \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{K}\left(r, v, n\right) = \operatorname{pathsFrom}\left(\operatorname{G}\left(n\right), r, v, n\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.K` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 16: “Definition 5.4. Let Kℓ,v,n be the number of paths of length ℓ in Gn that start at a vertex labeled v and end at a vertex labeled n. For a given n, the table of Kℓ,v,n for all values of ℓ and v is called the n-table.” r is the path length ℓ. The source's example K₁,₂,₃ counts all starting vertices labeled 2 and gives 2×2 + 2×2×2 = 12. K is a natural number; its occurrence in the conjectured weighted sum is explicitly cast to ℚ.

**Definition 1.7 (Super Catalan numbers).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{S}\left(m, n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot m\right):\mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right):\mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(m\right):\mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n\right):\mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(m + n\right):\mathbb{Q})}$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.S` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 15: “Definition 5.1 ([1], A17). The super Catalan numbers are defined by S(m, n) = (2m)!(2n)! / (m!n!(m + n)!).” Both arguments are natural numbers. Each factorial is cast to ℚ before rational multiplication and division.

**Definition 1.8 (Caldwell and coauthors' conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \operatorname{S}\left(0, n + 1\right) = \sum_{r \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (\frac{(2:\mathbb{Q})}{(2:\mathbb{Q})^{r}} \cdot \sum_{v \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} ((\operatorname{K}\left(r, v, n\right):\mathbb{Q}))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.claim` (`✓ std3`).

*Citation.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

ArXiv v1, page 17: “Conjecture 5.6. The subsequent super Catalan number can be computed from the n-table of its previous action graph via S(0, n + 1) = Σ_{ℓ=0}^{n} (2/2^ℓ) Σ_{v=0}^{n} Kℓ,v,n.” The quantifier includes n = 0. Both finite sums range from zero through n, and the weights and path counts are interpreted in ℚ.

**Theorem 1.9 (Proof of the weighted column identity).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor, S. Klanderman, A. Tebbe (2024). *Catalan Number Sequences and Generalized Action Graphs*. DOI: [10.48550/arXiv.2507.22719](https://doi.org/10.48550/arXiv.2507.22719). URL: <https://arxiv.org/abs/2507.22719v1>.

*Commentary.*

At every subtree, 2^r divides the number of length-r paths to the current generation. This makes every growth count an exact quotient. Removing the last edge gives the weighted path recurrence. Summing over starting vertices and inducting on n yields the column formula 2^r times Nat.choose(2n − r, n) for 0 ≤ r ≤ n. The hockey-stick identity then gives twice Nat.choose(2n + 1, n + 1), equal to S(0, n + 1). The per-label path recurrence of Conjecture 5.5 has a posted proof at MathDB p/369567; the same last-edge mechanism supplies the recurrence used here.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.G`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.K`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.S`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.Tree`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.grow`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.paths`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.pathsFrom`
- Truth anchor: `D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.result`
