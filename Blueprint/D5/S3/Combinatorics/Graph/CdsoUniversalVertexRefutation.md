# A CDSO minimizer without a universal vertex

## Abstract

Among connected simple graphs of order seven and cyclomatic number one, every CDSO minimizer lacks a vertex adjacent to all others. A triangle with three leaves at one vertex and one leaf at a second vertex has strictly smaller CDSO than every graph with a universal vertex.

**Definition 1.1 (The complementary diminished Sombor index).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], \forall (h : \forall (u : \operatorname{Fin}\left(n\right)), \forall (v : \operatorname{Fin}\left(n\right)), \frac{\operatorname{Real.sqrt}\left((\operatorname{SimpleGraph.degree}\left(G, u\right) : \mathbb{R})^{2} + (\operatorname{SimpleGraph.degree}\left(G, v\right) : \mathbb{R})^{2}\right)}{\operatorname{max}\left((\operatorname{SimpleGraph.degree}\left(G, u\right) : \mathbb{R}), (\operatorname{SimpleGraph.degree}\left(G, v\right) : \mathbb{R})\right)} = \frac{\operatorname{Real.sqrt}\left((\operatorname{SimpleGraph.degree}\left(G, v\right) : \mathbb{R})^{2} + (\operatorname{SimpleGraph.degree}\left(G, u\right) : \mathbb{R})^{2}\right)}{\operatorname{max}\left((\operatorname{SimpleGraph.degree}\left(G, v\right) : \mathbb{R}), (\operatorname{SimpleGraph.degree}\left(G, u\right) : \mathbb{R})\right)}), \operatorname{cdso}\left(G\right) = \sum_{e \in \operatorname{SimpleGraph.edgeFinset}\left(G\right)} \operatorname{Sym2.lift}\left(\langle\lambda (u : \operatorname{Fin}\left(n\right)) \mapsto \lambda (v : \operatorname{Fin}\left(n\right)) \mapsto \frac{\operatorname{Real.sqrt}\left((\operatorname{SimpleGraph.degree}\left(G, u\right) : \mathbb{R})^{2} + (\operatorname{SimpleGraph.degree}\left(G, v\right) : \mathbb{R})^{2}\right)}{\operatorname{max}\left((\operatorname{SimpleGraph.degree}\left(G, u\right) : \mathbb{R}), (\operatorname{SimpleGraph.degree}\left(G, v\right) : \mathbb{R})\right)}, h\rangle\right)\left(e\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.cdso` (`✓ std3`).

*Citation.* A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza (2025). *On the hyperbolic Sombor index and its counterpart*. DOI: [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176). URL: <https://www.dmlett.com/archive/v16/DML25_v16_pp108-115.pdf>.

*Commentary.*

Page 109: "We drop the factor 1/√2 from the expression (1) and call the resulting formula the complementary diminished Sombor (CDSO) index and denote it by ᶜDSO. Hence, for a graph G, we have", followed by the sum of sqrt(d(u)²+d(v)²)/max{d(u),d(v)} over uv in E(G). SimpleGraph.degree is cast to the reals before squaring and division. SimpleGraph.edgeFinset contains each unordered edge once. Sym2.lift evaluates the symmetric function on its two endpoints; the anonymous proof stored by Lean may be replaced by any h of the displayed symmetry type, by proof irrelevance. The lambda expressions bind both endpoints with type Fin n. Every edge has two positive endpoint degrees, so its maximum degree is positive.

**Definition 1.2 (The literal cyclomatic number).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], \operatorname{cyclomaticNumber}\left(G\right) = \operatorname{sInf}\left(\{k : \mathbb{N} \mid \exists (s : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), (s \subseteq \operatorname{SimpleGraph.edgeFinset}\left(G\right)) \land ((\operatorname{Finset.card}\left(s\right) = k) \land (\operatorname{SimpleGraph.IsAcyclic}\left(\operatorname{SimpleGraph.deleteEdges}\left(G, (s : \operatorname{Set}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right))\right)\right)))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.cyclomaticNumber` (`✓ std3`).

*Citation.* A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza (2025). *On the hyperbolic Sombor index and its counterpart*. DOI: [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176). URL: <https://www.dmlett.com/archive/v16/DML25_v16_pp108-115.pdf>.

*Commentary.*

Page 115: "We recall that trees can be considered connected graphs of cyclomatic number 0, where the cyclomatic number of a graph is the minimum number of edges whose removal makes the graph acyclic." The set consists of the cardinalities of edge subsets whose deletion yields SimpleGraph.IsAcyclic, the absence of cyclic walks. It is nonempty because deleting all edges gives the empty graph. Its natural-number infimum is therefore its minimum. The formula explicitly coerces the finite deletion set to a set of unordered pairs. For a connected graph, extension of an acyclic subgraph to a spanning tree and the tree edge-count theorem identify this minimum through cyclomaticNumber G + n = card(edgeFinset G) + 1.

**Definition 1.3 (The CDSO half of Conjecture 4.1).**

$$claim \Leftrightarrow (\forall (n : \mathbb{N}), \forall (ell : \mathbb{N}), (1 \le ell) \Rightarrow (\forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\operatorname{SimpleGraph.Connected}\left(G\right)) \Rightarrow ((\operatorname{cyclomaticNumber}\left(G\right) = ell) \Rightarrow ((\forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(H\right)\right)], (\operatorname{SimpleGraph.Connected}\left(H\right)) \Rightarrow ((\operatorname{cyclomaticNumber}\left(H\right) = ell) \Rightarrow (\operatorname{cdso}\left(G\right) \le \operatorname{cdso}\left(H\right)))) \Rightarrow (\exists (v : \operatorname{Fin}\left(n\right)), \forall (w : \operatorname{Fin}\left(n\right)), (\neg w = v) \Rightarrow (\operatorname{SimpleGraph.Adj}\left(G, v, w\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.claim` (`✓ std3`).

*Citation.* A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza (2025). *On the hyperbolic Sombor index and its counterpart*. DOI: [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176). URL: <https://www.dmlett.com/archive/v16/DML25_v16_pp108-115.pdf>.

*Commentary.*

Page 115, Conjecture 4.1: "A graph minimizing (maximizing, respectively) the CDSO index (HSO index, respectively) among fixed-order connected graphs with cyclomatic number ℓ(≥ 1) has a vertex adjacent to all other vertices." This encoding states the CDSO half for every order n, every positive cyclomatic number ell, and every minimizer G. The comparison graph H ranges over the same connected class. Fin n labels the vertices, without restricting isomorphism types. Decidable adjacency selects finite-set representations and does not change the value of either invariant. A universal vertex v is adjacent to every w distinct from v. Refuting this half refutes the combined conjecture; the HSO half is not decided here.

**Theorem 1.4 (Refutation of the universal-vertex assertion).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/albalahi-das-ali-barman-hamza-2025-cdso-universal-vertex-refutation` (refuted) by `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"albalahi-das-ali-barman-hamza-2025-cdso-universal-vertex-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. M. Albalahi, S. Das, A. Ali, J. Barman, A. E. Hamza (2025). *On the hyperbolic Sombor index and its counterpart*. DOI: [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176). URL: <https://www.dmlett.com/archive/v16/DML25_v16_pp108-115.pdf>.

*Commentary.*

On vertices 0 through 6, take the edges 01, 02, 12, 03, 04, 05 and 16. The graph is connected, has seven edges and cyclomatic number one, and its degrees are 5, 3, 2, 1, 1, 1, 1. Its CDSO is sqrt(10)/3 + sqrt(29)/5 + sqrt(34)/5 + sqrt(13)/3 + 3 sqrt(26)/5. A universal vertex in any graph of this class accounts for six edges; the unique remaining edge joins two other vertices. Relabelling thus gives the star centred at 0 with the additional edge 12, whose CDSO is sqrt(2) + 2 sqrt(10)/3 + 2 sqrt(37)/3. Rational bounds on the square roots prove a strict inequality between these two values. The finite nonempty class has a minimizer, whose value is at most the first value. Consequently every minimizer lacks a universal vertex. No assertion of uniqueness of the minimizer is needed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.cdso`
- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.cyclomaticNumber`
- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.result`
