# A directed graph with democracy coefficient above one

## Abstract

A weakly connected directed graph on six vertices with twelve unweighted arcs has forward hierarchical levels (227, -991, -991, 329, 767, 659)/2694 and forward democracy coefficient 901/898, which is larger than 1. This refutes Conjecture 3.6 of G. Moutsinas, C. Shuaib, W. Guo and S. Jarvis (arXiv:1908.04358), which asserts that the democracy coefficients of every weakly connected directed graph are at most 1.

**Definition 1.1 (The weighted in-degree).**

$$\operatorname{indeg}\left(A, j\right) = \sum_{i} A\left(i, j\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.indeg` (`✓ std3`).

*Citation.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

For a matrix A of non-negative arc weights on n vertices, with a_ij > 0 exactly when there is an arc from i to j, the weighted in-degree of vertex j is d_j, the sum over i of a_ij.

**Definition 1.2 (The transposed in-degree Laplacian).**

$$\operatorname{lapT}\left(A\right) = (\operatorname{diag}\left(\operatorname{indeg}\left(A\right)\right) - A)^{T}$$

*Formalization.* `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.lapT` (`✓ std3`).

*Citation.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

M is the transpose of the in-degree Laplacian L = diag(d) - A.

**Definition 1.3 (The residual).**

$$\operatorname{residual}\left(A, x\right) = \left\lVert \operatorname{lapT}\left(A\right) \cdot x - \operatorname{indeg}\left(A\right) \right\rVert_{2}$$

*Formalization.* `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.residual` (`✓ std3`).

*Citation.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

For a vector x in R^n, the residual is the Euclidean norm of M x - d.

**Definition 1.4 (Forward hierarchical levels).**

$$\operatorname{IsForwardLevels}\left(A, g\right) \Leftrightarrow ((\forall x \in \mathbb{R}^{n}, \operatorname{residual}\left(A, g\right) \le \operatorname{residual}\left(A, x\right)) \land (\forall x \in \mathbb{R}^{n}, (\forall y \in \mathbb{R}^{n}, \operatorname{residual}\left(A, x\right) \le \operatorname{residual}\left(A, y\right)) \Rightarrow \left\lVert g \right\rVert_{2} \le \left\lVert x \right\rVert_{2}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.IsForwardLevels` (`✓ std3`).

*Citation.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

A vector g is a vector of forward hierarchical levels (Definition 3.1 of the paper) when it minimizes the residual and, among all minimizers of the residual, has the least Euclidean norm.

**Definition 1.5 (The forward democracy coefficient).**

$$\operatorname{forwardDemocracy}\left(A, g\right) = 1 - \frac{\sum_{i} \sum_{j} A\left(i, j\right) \cdot (g_{j} - g_{i})}{\sum_{i} \sum_{j} A\left(i, j\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.forwardDemocracy` (`✓ std3`).

*Citation.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

The forward democracy coefficient is 1 minus the mean of the differences g_j - g_i over the arcs from i to j, the mean being weighted by a_ij.

**Definition 1.6 (Weak connectivity).**

$$\operatorname{WeaklyConnected}\left(A\right) \Leftrightarrow (\operatorname{Connected}\left(\operatorname{fromRel}\left(i, j \mapsto 0 < A\left(i, j\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.WeaklyConnected` (`✓ std3`).

*Citation.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

A is weakly connected when the undirected simple graph on the n vertices, in which distinct vertices i and j are adjacent exactly when a_ij > 0 or a_ji > 0, is connected.

**Definition 1.7 (Conjecture 3.6).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N}, \forall A \in \mathbb{R}^{n \times n}, (\forall i, j, 0 \le A\left(i, j\right)) \Rightarrow \left((\forall i, A\left(i, i\right) = 0) \Rightarrow \left((\operatorname{WeaklyConnected}\left(A\right)) \Rightarrow \forall g \in \mathbb{R}^{n}, (\operatorname{IsForwardLevels}\left(A, g\right)) \Rightarrow \operatorname{forwardDemocracy}\left(A, g\right) \le 1\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.claim` (`✓ std3`).

*Citation.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

The forward half of the first bullet of Conjecture 3.6: for every n and every matrix A of non-negative weights with zero diagonal whose arcs form a weakly connected graph, every vector g of forward hierarchical levels gives a forward democracy coefficient at most 1.

**Theorem 1.8 (A graph with coefficient 901/898).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/moutsinas-2021-democracy-coefficient-bound` (refuted) by `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"moutsinas-2021-democracy-coefficient-bound","declaration_gid":"D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis (2021). *Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks*. DOI: [10.1038/s41598-021-93161-4](https://doi.org/10.1038/s41598-021-93161-4). URL: <https://arxiv.org/abs/1908.04358v4>.

*Commentary.*

Take n = 6 and the unweighted arcs 1 -> 4, 1 -> 5, 2 -> 6, 3 -> 6, 4 -> 5, 4 -> 6, 5 -> 1, 5 -> 2, 5 -> 3, 5 -> 4, 6 -> 1, 6 -> 5; the adjacencies 1-4, 1-5, 5-2, 5-3, 5-6 make the graph weakly connected, and the in-degree vector is d = (2, 1, 1, 2, 3, 3). Let g = (227, -991, -991, 329, 767, 659)/2694. The six coordinates of the transpose of M applied to M g - d vanish, so for every x the square of the residual of x is the square of the residual of g plus the squared norm of M (x - g); hence g minimizes the residual. A minimizer x then has M (x - g) = 0, and the six coordinate equations of this system force all coordinates of x - g to be equal; since the coordinates of g sum to 0, the squared norm of x exceeds that of g by six times the square of the common difference, so g has the least norm among the minimizers. The sum of g_j - g_i over the twelve arcs is -18/449, so the forward democracy coefficient of g is 1 + 18/(449 * 12) = 901/898 > 1.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.IsForwardLevels`
- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.WeaklyConnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.forwardDemocracy`
- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.indeg`
- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.lapT`
- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.residual`
- Truth anchor: `D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.result`
