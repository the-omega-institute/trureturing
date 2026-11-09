# ZagrebInequality

## Abstract

The Zagreb inequality for the complete subgroup-generating graph.

**Definition 1.1 (First Zagreb index).**

$$\forall V \in \operatorname{Type},\; \forall finiteV \in \operatorname{Fintype}\left(V\right),\; \forall g \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{firstZagreb}\left(g\right):\mathbb{R}) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(V\right)), \operatorname{fun} (v:V) \mapsto (\operatorname{SimpleGraph}.\operatorname{degree}\left(g, v\right):\mathbb{R})^{2}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.firstZagreb` (`✓ std3`).

*Citation.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2025). *Zagreb indices of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2501.06124](https://doi.org/10.48550/arXiv.2501.06124). URL: <https://arxiv.org/abs/2501.06124v1>.

*Commentary.*

For a finite simple graph, the first Zagreb index is the real sum of squared degrees over every vertex. Isolated vertices stay in the carrier and contribute zero.

**Definition 1.2 (Unordered endpoint product).**

$$\forall V \in \operatorname{Type},\; \forall finiteV \in \operatorname{Fintype}\left(V\right),\; \forall g \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{endpointProduct}\left(g\right):\operatorname{Sym2}\left(V\right) \to \mathbb{R}) = \operatorname{Sym2}.\operatorname{lift}\left(\langle\operatorname{fun} (u:V) \mapsto \operatorname{fun} (v:V) \mapsto (\operatorname{SimpleGraph}.\operatorname{degree}\left(g, u\right):\mathbb{R}) \cdot (\operatorname{SimpleGraph}.\operatorname{degree}\left(g, v\right):\mathbb{R}), \operatorname{fun} (u:V) \mapsto \operatorname{fun} (v:V) \mapsto \operatorname{mul_{comm}}\left((\operatorname{SimpleGraph}.\operatorname{degree}\left(g, u\right):\mathbb{R}), (\operatorname{SimpleGraph}.\operatorname{degree}\left(g, v\right):\mathbb{R})\right)\rangle\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.endpointProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2025). *Zagreb indices of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2501.06124](https://doi.org/10.48550/arXiv.2501.06124). URL: <https://arxiv.org/abs/2501.06124v1>.

*Commentary.*

Multiplication of endpoint degrees is symmetric, so it defines a real function on unordered vertex pairs.

**Definition 1.3 (Second Zagreb index).**

$$\forall V \in \operatorname{Type},\; \forall finiteV \in \operatorname{Fintype}\left(V\right),\; \forall g \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{secondZagreb}\left(g\right):\mathbb{R}) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(g\right), \operatorname{fun} (e:\operatorname{Sym2}\left(V\right)) \mapsto \operatorname{endpointProduct}\left(g, e\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.secondZagreb` (`✓ std3`).

*Citation.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2025). *Zagreb indices of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2501.06124](https://doi.org/10.48550/arXiv.2501.06124). URL: <https://arxiv.org/abs/2501.06124v1>.

*Commentary.*

The second Zagreb index sums the endpoint product over the actual unordered edge finset. Each edge occurs once.

**Theorem 1.4 (All finite groups).**

$$\forall G \in \operatorname{Type},\; \forall groupG \in \operatorname{Group}\left(G\right),\; \forall finiteG \in \operatorname{Fintype}\left(G\right),\; \frac{\operatorname{firstZagreb}\left(\operatorname{sgbGraph}\left(G\right)\right)}{(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(G\right)\right):\mathbb{R})} \le \frac{\operatorname{secondZagreb}\left(\operatorname{sgbGraph}\left(G\right)\right)}{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(\operatorname{sgbGraph}\left(G\right)\right)\right):\mathbb{R})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.hansen_vukicevic` (`✓ std3`). ∎

*Resolves.* `Problems/das-erfanian-nath-2025-sgb-zagreb-problem310` (proved) by `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.hansen_vukicevic`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"das-erfanian-nath-2025-sgb-zagreb-problem310","declaration_gid":"D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.hansen_vukicevic","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shrabani Das; Ahmad Erfanian; Rajat Kanti Nath (2025). *Zagreb indices of subgroup generating bipartite graph*. DOI: [10.48550/arXiv.2501.06124](https://doi.org/10.48550/arXiv.2501.06124). URL: <https://arxiv.org/abs/2501.06124v1>.

*Commentary.*

For every finite group, the second Zagreb index divided by the edge count is at least the first Zagreb index divided by the vertex count. The graph has disjoint vertex parts consisting of all ordered pairs and all subgroups, with a pair adjacent precisely to the subgroup it generates. Repetitions and zero fibers are retained. There is no nonabelian, nontrivial or two-generator assumption.

Write m for the square of the group order, k for the number of all subgroups, and r(H) for the number of ordered pairs generating H. The existing pair partition gives the sum of r(H) as m. The original degree identities give degree one at every pair vertex and degree r(H) at H. An injective map sends each ordered pair to its one unordered graph edge and its image is exactly the edge finset. Consequently the first index is m plus the sum of r(H) squared, and the second index is the sum of r(H) squared. The vertex count is m plus k and the edge count is m; both are positive, including for the trivial group.

Source correspondence: Das, Erfanian and Nath, arXiv:2501.06124v1, Theorem 3.1 gives the two index formulas using Pr_H(G)=r(H)/m; Theorem 3.2 gives the edge and degree sums; Theorem 3.3 gives the equivalent criterion k times the sum of Pr_H(G) squared at least one. These are known source identities. The formal bridge uses the inherited literal graph, sum_pairCount, edge_count, degree_pair and degree_subgroup directly; the last two are the original supplier declarations made public. Their separate parent delivery and authorship are not claimed here.

Mathlib's sq_sum_le_card_mul_sum_sq states that m squared is at most k times the sum of r(H) squared. Clearing the two positive denominators yields the stated comparison, so the answer to the full existential Problem 3.10, printed page 13, is NO. All five theorems in this module are bind-only. The private pairEdge_injective and actual_edges are consumed by second_formula; first_formula and second_formula are consumed by hansen_vukicevic. The endpoint's admission basis is open-problem-resolution; neither it nor the consumed helpers supplies new escape content. This theorem makes no claim about arbitrary forests.

The retained Reg mirror compiles but its binding audit is declared_unresolved: IE-C050 ClosedTruthReadout, unclassified_form:source.coordinate_dependency, missing=0;selected=#[3];scope=4. The concrete unfinished-audit exception is https://github.com/the-omega-institute/trureturing/issues/28349#issuecomment-6731659148. The prospective event is https://github.com/the-omega-institute/trureturing/issues/28349#issuecomment-6731353916. The full resolution metadata names one exact frozen theorem. Final independent publication review, required CI, merge and first-dev verification remain delivery obligations; no official settlement, priority or solved-problem KPI is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.endpointProduct`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.firstZagreb`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.hansen_vukicevic`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.secondZagreb`
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/FiberSpectra](FiberSpectra.md)
