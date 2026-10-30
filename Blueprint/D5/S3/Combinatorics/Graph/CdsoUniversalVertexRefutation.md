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

## Actual incidence arrays and the scale of a uniform gap

Let a be any integer at least four, r=a+1 and s=a+2. The finite labels are Fin s; adding one to their values identifies them with [s]. The extra label e is the last element and H is its complement, of cardinality a+1. For every real epsilon with 0<epsilon<=1/a, give {e} mass epsilon, H mass (a-1)epsilon, and H with j removed mass (1-a epsilon)/(a+1) for each j in H. Every other subset has mass zero. In particular the empty subset has mass zero, so the array is a probability law on all nonempty subsets. Fintype.sum_subtype_add_sum_subtype identifies every expectation over that subtype with the finite sum on all subsets; its empty-subset term vanishes.

The law has nonnegative masses, total mass one, zero empty mass and positive marginals. The mean, marginals, moments and energy are finite expectations under that single law: q=sum_T x_T |T|, y_i=sum_{T containing i} x_T, w_i=sum_{T containing i} x_T |T|^2, and 2J=sum_i w_i/y_i^2. No independently chosen marginal or relaxed pair law enters these definitions.

The total mass is epsilon+(a-1)epsilon+1-a epsilon=1, and the cardinality mean is epsilon+(a+1)(a-1)epsilon+a(1-a epsilon)=a. On H, y_i=(a-epsilon)/(a+1) and w_i=(a^3+epsilon E_a)/(a+1), where E_a=2a^3-2a-1. At the extra label, y_e=w_e=epsilon. Consequently all marginals are positive, including the extra marginal. The original adjacent-cardinality benchmark is F_r(q)=r^2((3(r-1)^2+3(r-1)+1)q-(r-1)r(2r-1))/(2q^2).

The exact energy is 2J=(a+1)^2(a^3+epsilon E_a)/(a-epsilon)^2+1/epsilon. Writing A_a=2a^3+2a^2-2a-1, the exact difference is 2(J-F_{a+1}(a))=1/epsilon+(a+1)^2 epsilon(A_a-a epsilon)/(a-epsilon)^2. Here a epsilon<=1, A_a>1 and a-epsilon>0, so both terms are strictly positive throughout the stated domain.

Support connectivity is the reflexive transitive closure of sharing a positive-mass type. Two labels are connected exactly when either both equal e or neither equals e. H is nonempty and its full type has positive mass; {e} also has positive mass, and no positive-mass type crosses the partition. Thus these are exactly two actual support components. At epsilon=1/a the missing-one masses are zero, while this support conclusion and every positive marginal persist.

Put epsilon_a=1/(sqrt(2) a^(3/2)), with the real power and a tending to infinity through natural numbers. This parameter is admissible for every a>=4. Both (J-F_{a+1}(a))/a^(3/2) and (J-F_{a+1}(a))/(a+1)^(3/2) tend to sqrt(2). The difference divided by (a+1)^2 therefore tends to zero. The rational infinite subfamily in the source is a=2b^2, epsilon=1/(4b^3), for integers b>=2; it has the same scale.

There is no real c>0 for which J_s(x)-F_r(q)>=c r^2 holds for every integer r>=5, every finite integer s>=r+1, and every actual profile on [s] whose mean belongs to [r-1,r]. Indeed apply such a bound to these profiles with r=a+1, s=a+2 and q=a, and divide by the positive square r^2. The resulting lower bound c contradicts convergence to zero.

Mathlib finite-sum interchange and Finset.card_erase_of_mem compute the cardinality of an erased finite set, the masses, the mean and the moments. Positive support types preserve the core/extra partition along every incidence path by Relation.ReflTransGen.mono and Relation.reflTransGen_eq_self; the full core type connects every core pair. Subtracting the native benchmark gives the displayed gap. For the limits, divide by a^(3/2), use its square a^3, and obtain 1/sqrt(2)+(1+1/a)^2(2+2/a-2/a^2-1/a^3-epsilon_a/a^2)/(2 sqrt(2)(1-epsilon_a/a)^2). Express this through 1/a and epsilon_a/a, both tending to zero by tendsto_inv_atTop_zero and tendsto_rpow_neg_atTop. Filter.Tendsto.div and continuity of real powers give the first limit, and tendsto_natCast_div_add_atTop gives the second after Real.div_rpow. Real.rpow_add and Real.sqrt_eq_rpow identify the rational subfamily; composition along b mapped to 2b^2 transfers both limits.

This is a repository derivation for probability arrays. It asserts neither optimality of this family nor an exact connected graph realization at every finite budget. Its support is disconnected. A prescribed-budget graph realization requires its separate fixed-parameter, capacity and positive-marginal hypotheses. The cdso definition above fixes the original graph normalization. The graph refutation is not a premise for the array inference. No external literature-priority claim is made for the array construction or its consequences.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.cdso`
- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.cyclomaticNumber`
- Truth anchor: `D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.result`
