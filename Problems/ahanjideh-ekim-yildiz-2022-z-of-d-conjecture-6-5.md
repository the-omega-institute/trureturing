---
slug: ahanjideh-ekim-yildiz-2022-z-of-d-conjecture-6-5
bibkey: ahanjidehekimyildiz2022matching
doi: 10.1007/s10878-024-01123-z
url: https://arxiv.org/abs/2207.02271v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ComponentPacking/AhanjidehEkimYildizZ.result
---

# The extremal matching number of almost regular triangle-free graphs

## Problem

M. Ahanjideh, T. Ekim and M. A. Yıldız, *Maximum size of a triangle-free graph with bounded maximum degree and matching number*, arXiv:2207.02271v1, Conjecture 6.5:

> For d ≥ 21 and odd, we have Z(d) = ⌊5(d + 1)/4⌋.

The journal locator is DOI 10.1007/s10878-024-01123-z. The quotations refer to version 1. The source defines $Z(d)$, for $d\ge2$, as the least matching number of a triangle-free factor-critical graph that is regular of degree $d$ when $d$ is even, and almost regular of degree $d$ when $d$ is odd.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| “if d(w) = d − 1 for some w ∈ V(G) and d(v) = d for all v ∈ V(G) − w, then G is said to be almost d-regular.” | `FactorCriticalMatching.IsAlmostRegular` | One deficient vertex and every other degree are specified literally. |
| “A graph G is said to be factor-critical if G \\ v has a perfect matching for all v ∈ V(G).” | `FactorCriticalMatching.IsFactorCritical` | Perfect subgraph matchings in each induced vertex complement. |
| “For any d ≥ 2, let Z(d) be the smallest natural number n such that there exists a d-regular (if d is even) or almost d-regular (if d is odd) triangle-free and factor-critical graph G with ν(G) = n.” | `AhanjidehEkimYildizZ.Z` | Natural infimum of exactly those matching-number witnesses. |
| “For d ≥ 21 and odd, we have Z(d) = ⌊5(d + 1)/4⌋.” | `AhanjidehEkimYildizZ.claim` and `.result` | Every odd natural degree at least 21; natural division is the floor. |

Finite simple graphs have carrier `Fin n`; the matching number is the existing `DimerVirialFourthDifferenceRefutation.matchingNumber`. The formal definition of $Z$ is total on natural numbers and admits an empty carrier. The proved range has a deficient vertex and is nonempty. No statement about the paper's convention at even or small degrees is inferred from this total extension.

## Motivation

The source's Lemma 4.7 brackets $Z(d)$ between $\lfloor5(d-1)/4\rfloor$ and $\lfloor5(d+1)/4\rfloor$ for odd $d$. The result identifies the endpoint for every odd $d\ge21$. The two odd residue classes have uniform extremal constructions, while the lower bound rules out smaller orders.

## Gap

Preregistration #19633 gives the source quotation, quantified conventions and literature screen. The inspected Banak–Ekim–Taşkın arXiv:2304.01729v1 gives small cases and leaves the target range unsettled. The original source's full journal text and all later literature have not been exhaustively verified. Literature status is `not-found-in-searched-scope`; completeness is `ASSUMED-UNVERIFIED`.

The structural input is the strict three-eighths theorem of Häggkvist: every finite triangle-free graph with $3|V|<8\delta$ admits a homomorphism to the pentagon. Its source is identified in `Library/GraphInvariants/haggkvist1982oddcycles.md`; the original chapter's full text is unverified. The delivered graph modules prove the structural reduction from finite counting.

## Route

Factor-criticality identifies the order as twice the matching number plus one. Below the proposed bound, the three-eighths inequality gives a pentagon homomorphism except at degree 23 and order 59. In that exception, deletion of the deficient vertex permits the density theorem; an independent support argument extends the map to the deleted vertex. Nonbipartiteness forces the pentagon map to be surjective.

Write $s_i$ for the five class sizes, $t_i=s_{i-1}+s_{i+1}$ and $u_i=t_i-d$. The total slack can only be one or three. Missing edges give cyclic incidence equations whose independent-set inequalities contradict every slack pattern. This proves the lower bound. Dense balanced Hall matchings supply the almost regular pentagon constructions for both odd residue classes, giving attainment and the matching upper bound. Natural-infimum composition yields the exact equality.

## Falsifier

The exact target is false if an odd $d\ge21$ has an admissible graph with matching number below $\lfloor5(d+1)/4\rfloor$, or if no admissible graph attains that number. The kernel-checked lower obstruction and uniform attainment exclude these two possibilities in the formal finite-simple-graph model. No axiom asserting a graph-structure theorem is added.

## Evidence

The settling declaration is `D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ.result`. Its Scribe displays the entire quantified equality. Each supporting module has its own canonical state record under `Golden/Frozen/state/`; the modified Dimer owner and its affected frozen importer are maintained by the canonical writer.

The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}.

### Experiment

[Exact finite checks](https://github.com/the-omega-institute/trureturing-experiments/tree/934ef3827cb10cc50d6bbc9bdddae02c30025174/docs/reports/ahanjideh-ekim-yildiz-2022-z-of-d-odd-conjecture-6-5) contain the independent program and results. The script `check.py` has SHA-256 `e66ffd72eab1d44edba7d8a5d51ae7904ad8e413ba460f7a5f412e15f32605d6`. Running `python3 docs/reports/ahanjideh-ekim-yildiz-2022-z-of-d-odd-conjecture-6-5/check.py` in that experiment checkout with NetworkX 3.7 exits 0 (`RESULT PASS`). The implementation seat measured this with its isolated Python interpreter.

The construction checks cover exactly $d=21,23,25,27,29,31$, with orders $55,61,65,71,75,81$ and matching numbers $27,30,32,35,37,40$. At $d=23$, order 59, all 2310 feasible pairs $(a,w)$ have independent support. The slack tests cover $U=1$ with $11\le C\le60$, and $U=3$ with $13\le C\le60$, every composition and deficient class; no pattern survives all independent-set inequalities. The arithmetic tests cover odd $d$ from 21 through 401. These finite computations do not establish the unbounded theorem; the Lean proofs do.

### Escape audit

The four-slot escape audit is unfinished in [#20094](https://github.com/the-omega-institute/trureturing/issues/20094). Faithful dependent-family reconstruction, exact bridges, variation, sensitivity and actual observational dependence have not been established. No registration is reported as `declared_validated`.

## Triage

Tier 1 published conjecture. Settlement **Proved**, admission basis `open-problem-resolution (#19633; Proved)`. The existing Dimer refutation retains `open-problem-resolution (issue #12197; Refuted)` and its own dossier and resolution node.

### What the settlement shows

- **Kernel-checked:** `AhanjidehEkimYildizZ.result` proves $Z(d)=\lfloor5(d+1)/4\rfloor$ for every odd $d\ge21$.
- **Kernel-checked:** `PentagonMissingEdgeObstruction.PentagonSurjectiveLower.no_small_surjective_map` excludes the smaller odd orders for a surjective pentagon map with the almost regular degree pattern. The decisive obstruction is the incompatibility of missing-edge incidence with total slack one or three.
- **Kernel-checked:** `PentagonMissingEdgeObstruction.OrderArithmetic.threshold_or_exception` isolates the degree-23, order-59 exception. The proof of `AhanjidehEkimYildizZ.ExceptionalLower.no_order_59` excludes it by vertex deletion, independent support and extension.
- **Kernel-checked:** `AhanjidehEkimYildizZUpper.AEYUpperAttainment.attainment` constructs triangle-free factor-critical witnesses attaining the bound for both odd residue classes. Its proof uses the degree-row identities `ConstructionRows.degree_small` and `.degree_large` and the consumed factor-critical matching construction.
- **Kernel-checked proof step:** `AhanjidehEkimYildizZ.AEYInfimum.Z_eq_of_attainment` composes the lower bound and attainment, including the equality transport between decidability instances. No mathematical obligation remains for the stated conjecture.
- **Literature reading:** the source's Lemma 4.7 gives the two-sided partial bound; Banak–Ekim–Taşkın, Section 2, lists $Z(d)=d$ for $d=2,3$ and $Z(d)=d+1$ for $d=4,5$. These are cited source statements, not additional Lean theorems of this delivery. The proposed formula already fails at $d=3,5$; the present theorem asserts no uniform extension to small odd degrees.
- **Proved in prose, conditional on the source's Theorem 4.8:** that theorem states $f_M(d,m)=dm+\lfloor d/2\rfloor$ when $Z(d)\le m<2d$. Substituting the established equality gives its explicit interval $\lfloor5(d+1)/4\rfloor\le m<2d$ for odd $d\ge21$. Theorem 4.8 itself is not formalized here.
- **Computed:** the finite construction, exceptional-support, slack and arithmetic readings have exactly the scopes in the Experiment entry. Uniform validity beyond those experimental scopes is supplied only where a named Lean theorem above states it.
- **Open:** extensions outside odd $d\ge21$, independent formal verification of the source's other results, and the four-slot registration evidence in #20094.

### Declaration classification

The module labels below expand to the following Lean namespace prefixes:

- `dense`: `D5.S3.Combinatorics.Graph.Walks.DenseTriangleFreeConfigurations`.
- `hagg`: `D5.S3.Combinatorics.Graph.Walks.HaggkvistPentagonHomomorphism`.
- `matching`: `D5.S3.Combinatorics.Graph.ComponentPacking.FactorCriticalMatching`.
- `obstruction`: `D5.S3.Combinatorics.Graph.ComponentPacking.PentagonMissingEdgeObstruction`.
- `upper`: `D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZUpper`.
- `settlement`: `D5.S3.Combinatorics.Graph.ComponentPacking.AhanjidehEkimYildizZ`.
- `dimer`: `D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation`.

Classifications expand same-delivery helpers and compiler-generated constants, with the frozen base and pinned Mathlib as the stopping boundary. Fixed closed certificate checks are bind-only consumed helpers.

| Module | Declaration | proof_shape | escape_witness | Direct consumers |
| --- | --- | --- | --- | --- |
| dense | `HaggFinitePatterns.A3Edges` | bind-only | `none` | dense.HaggFinitePatterns.A3, dense.HaggFinitePatterns.instDecidableAdjA3, dense.HaggLocalConfigurations.twin_edge_zero_two |
| dense | `HaggFinitePatterns.MycEdges` | bind-only | `none` | dense.HaggFinitePatterns.Myc, dense.HaggFinitePatterns.instDecidableAdjMyc, dense.HaggLocalConfigurations.myc_of_hexagon_configuration |
| dense | `HaggFinitePatterns.A3` | bind-only | `none` | dense.HaggFinitePatterns.a3_independent_bound, dense.HaggFinitePatterns.instDecidableAdjA3, dense.HaggForbidden.no_a3, dense.HaggLocalConfigurations.twin_edge_zero_two, hagg.HaggAttachment.transfer_twin, hagg.HaggAttachment.twin_edge, hagg.HaggFullAttachment.attachment_with_neighbor, hagg.HaggFullAttachment.attachment_zero, hagg.HaggFullAttachment.every_vertex_twin, hagg.HaggFullAttachment.pentagon_partition |
| dense | `HaggFinitePatterns.instDecidableAdjA3` | bind-only | `none` | dense.HaggFinitePatterns.a3_independent_bound |
| dense | `HaggFinitePatterns.Myc` | bind-only | `none` | dense.HaggFinitePatterns.instDecidableAdjMyc, dense.HaggFinitePatterns.myc_independent_bound, dense.HaggForbidden.no_myc, dense.HaggHexagon.myc_of_anchor, dense.HaggHexagon.myc_of_hexagon, dense.HaggHexagon.no_hexagon, dense.HaggLocalConfigurations.myc_of_hexagon_configuration |
| dense | `HaggFinitePatterns.instDecidableAdjMyc` | bind-only | `none` | dense.HaggFinitePatterns.myc_independent_bound |
| dense | `HaggFinitePatterns.mycWeight` | bind-only | `none` | dense.HaggFinitePatterns.myc_independent_bound, dense.HaggFinitePatterns.myc_total_weight, dense.HaggForbidden.no_myc |
| dense | `HaggFinitePatterns.a3_independent_bound` | bind-only | `none` | dense.HaggForbidden.no_a3 |
| dense | `HaggFinitePatterns.myc_independent_bound` | bind-only | `none` | dense.HaggForbidden.no_myc |
| dense | `HaggFinitePatterns.myc_total_weight` | bind-only | `none` | dense.HaggForbidden.no_myc |
| dense | `HaggLocalConfigurations.pentagon_edge_iff` | bind-only | `none` | dense.HaggLocalConfigurations.twin_edge_zero_two, dense.HaggLocalConfigurations.twin_of_two, hagg.HaggAttachment.base_twin, hagg.HaggAttachment.old_base_twin, hagg.HaggAttachment.twin_edge, hagg.HaggBipartiteAlternative.pentagon_of_missing_cross, hagg.HaggFullAttachment.attachment_zero, hagg.HaggFullAttachment.every_vertex_twin |
| dense | `HaggLocalConfigurations.Pentagon` | bind-only | `none` | dense.HaggLocalConfigurations.twin_edge_zero_two, dense.HaggLocalConfigurations.twin_of_two, hagg.HaggAttachment.base_twin, hagg.HaggAttachment.old_base_twin, hagg.HaggAttachment.replace_pentagon, hagg.HaggAttachment.transfer_twin, hagg.HaggAttachment.twin_edge, hagg.HaggBipartiteAlternative.pentagon_of_missing_cross, hagg.HaggBipartiteAlternative.two_sides_of_no_pentagon, hagg.HaggFullAttachment.adjacency_of_twins, hagg.HaggFullAttachment.attachment_with_neighbor, hagg.HaggFullAttachment.attachment_zero, hagg.HaggFullAttachment.base_transition, hagg.HaggFullAttachment.every_vertex_twin, hagg.HaggFullAttachment.pentagon_partition, hagg.HaggkvistDense.pentagon_hom |
| dense | `HaggLocalConfigurations.Twin` | bind-only | `none` | dense.HaggLocalConfigurations.twin_edge_zero_two, dense.HaggLocalConfigurations.twin_of_two, hagg.HaggAttachment.base_twin, hagg.HaggAttachment.old_base_twin, hagg.HaggAttachment.replace_pentagon, hagg.HaggAttachment.transfer_twin, hagg.HaggAttachment.twin_edge, hagg.HaggFullAttachment.adjacency_of_twins, hagg.HaggFullAttachment.attachment_with_neighbor, hagg.HaggFullAttachment.attachment_zero, hagg.HaggFullAttachment.every_vertex_twin, hagg.HaggFullAttachment.pentagon_partition |
| dense | `HaggLocalConfigurations.NoHex` | bind-only | `none` | dense.HaggHexagon.no_hexagon, dense.HaggLocalConfigurations.twin_edge_zero_two, hagg.HaggAttachment.transfer_twin, hagg.HaggAttachment.twin_edge, hagg.HaggFullAttachment.attachment_with_neighbor, hagg.HaggFullAttachment.attachment_zero, hagg.HaggFullAttachment.every_vertex_twin, hagg.HaggFullAttachment.pentagon_partition, hagg.HaggkvistDense.pentagon_hom |
| dense | `HaggLocalConfigurations.twin_of_two` | bind-only | `none` | hagg.HaggAttachment.base_twin, hagg.HaggFullAttachment.attachment_zero |
| dense | `HaggLocalConfigurations.myc_of_hexagon_configuration` | content | `dense.HaggLocalConfigurations.myc_of_hexagon_configuration` | dense.HaggHexagon.myc_of_anchor |
| dense | `HaggLocalConfigurations.twin_edge_zero_two` | content | `dense.HaggLocalConfigurations.twin_edge_zero_two` | hagg.HaggAttachment.twin_edge |
| dense | `DenseDegreeCounting.weighted_degree_identity` | bind-only | `none` | dense.DenseDegreeCounting.weighted_degree_bound |
| dense | `DenseDegreeCounting.weighted_degree_bound` | bind-only | `none` | dense.DenseDegreeCounting.exists_many_adjacent, dense.DenseDegreeCounting.hom_weighted_degree_bound |
| dense | `DenseDegreeCounting.hom_weighted_degree_bound` | bind-only | `none` | dense.HaggForbidden.no_a3, dense.HaggForbidden.no_myc |
| dense | `DenseDegreeCounting.exists_many_adjacent` | bind-only | `none` | dense.HaggForbidden.d2, dense.HaggForbidden.d3 |
| dense | `HaggForbidden.triangle_free_of_clique_free` | bind-only | `none` | settlement.VertexDeletionBridges.neighbors_independent, hagg.HaggkvistDense.pentagon_hom |
| dense | `HaggForbidden.no_a3` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| dense | `HaggForbidden.no_myc` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| dense | `HaggForbidden.d2` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| dense | `HaggForbidden.d3` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| dense | `HexIndependentPatterns.hexEdges` | bind-only | `none` | dense.HaggHexagon.hexagon_triple, dense.HexIndependentPatterns.Hex, dense.HexIndependentPatterns.instDecidableAdjHex |
| dense | `HexIndependentPatterns.seedEdges` | bind-only | `none` | dense.HaggHexagon.seed_quad, dense.HexIndependentPatterns.Seed, dense.HexIndependentPatterns.instDecidableAdjSeed |
| dense | `HexIndependentPatterns.Hex` | bind-only | `none` | dense.HaggHexagon.hexagon_triple, dense.HexIndependentPatterns.hex_patterns, dense.HexIndependentPatterns.instDecidableAdjHex |
| dense | `HexIndependentPatterns.instDecidableAdjHex` | bind-only | `none` | dense.HexIndependentPatterns.hex_patterns |
| dense | `HexIndependentPatterns.Seed` | bind-only | `none` | dense.HaggHexagon.seed_quad, dense.HexIndependentPatterns.instDecidableAdjSeed, dense.HexIndependentPatterns.seed_patterns |
| dense | `HexIndependentPatterns.instDecidableAdjSeed` | bind-only | `none` | dense.HexIndependentPatterns.seed_patterns |
| dense | `HexIndependentPatterns.hex_patterns` | bind-only | `none` | dense.HaggHexagon.hexagon_triple |
| dense | `HexIndependentPatterns.seed_patterns` | bind-only | `none` | dense.HaggHexagon.seed_quad |
| dense | `HaggHexagon.D2` | bind-only | `none` | dense.HaggHexagon.hexagon_triple, dense.HaggHexagon.myc_of_anchor, dense.HaggHexagon.myc_of_hexagon, dense.HaggHexagon.no_hexagon |
| dense | `HaggHexagon.D3` | bind-only | `none` | dense.HaggHexagon.myc_of_hexagon, dense.HaggHexagon.no_hexagon, dense.HaggHexagon.seed_quad |
| dense | `HaggHexagon.hexagon_triple` | content | `dense.HaggHexagon.hexagon_triple` | dense.HaggHexagon.myc_of_anchor, dense.HaggHexagon.no_hexagon |
| dense | `HaggHexagon.myc_of_anchor` | content | `dense.HaggHexagon.myc_of_anchor` | dense.HaggHexagon.myc_of_hexagon |
| dense | `HaggHexagon.seed_quad` | content | `dense.HaggHexagon.seed_quad` | dense.HaggHexagon.myc_of_hexagon |
| dense | `HaggHexagon.myc_of_hexagon` | content | `dense.HaggHexagon.myc_of_hexagon` | dense.HaggHexagon.no_hexagon |
| dense | `HaggHexagon.no_hexagon` | content | `dense.HaggHexagon.no_hexagon` | hagg.HaggkvistDense.pentagon_hom |
| hagg | `HaggMaximal.exists_edge_of_dense` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| hagg | `HaggMaximal.common_neighbor_of_maximal` | bind-only | `none` | hagg.HaggMaximal.common_neighbor_all |
| hagg | `HaggMaximal.common_neighbor_all` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| hagg | `HaggMaximal.maximal_completion` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| hagg | `HaggAttachment.edge_rotate` | bind-only | `none` | hagg.HaggAttachment.twin_edge, hagg.HaggFullAttachment.attachment_with_neighbor |
| hagg | `HaggAttachment.edge_symm` | bind-only | `none` | hagg.HaggAttachment.replace_pentagon, hagg.HaggAttachment.transfer_twin |
| hagg | `HaggAttachment.index_common` | bind-only | `none` | hagg.HaggAttachment.transfer_twin, hagg.HaggFullAttachment.adjacency_of_twins |
| hagg | `HaggAttachment.twin_edge` | content | `hagg.HaggAttachment.twin_edge` | hagg.HaggAttachment.transfer_twin |
| hagg | `HaggAttachment.base_twin` | bind-only | `none` | hagg.HaggAttachment.old_base_twin, hagg.HaggFullAttachment.attachment_zero |
| hagg | `HaggAttachment.replace_pentagon` | bind-only | `none` | hagg.HaggAttachment.transfer_twin, hagg.HaggFullAttachment.attachment_zero, hagg.HaggFullAttachment.every_vertex_twin |
| hagg | `HaggAttachment.old_base_twin` | bind-only | `none` | hagg.HaggAttachment.transfer_twin |
| hagg | `HaggAttachment.transfer_twin` | content | `hagg.HaggAttachment.transfer_twin` | hagg.HaggFullAttachment.attachment_zero, hagg.HaggFullAttachment.every_vertex_twin |
| hagg | `HaggFullAttachment.attachment_zero` | content | `hagg.HaggFullAttachment.attachment_zero` | hagg.HaggFullAttachment.attachment_with_neighbor |
| hagg | `HaggFullAttachment.base_transition` | bind-only | `none` | hagg.HaggFullAttachment.attachment_with_neighbor |
| hagg | `HaggFullAttachment.attachment_with_neighbor` | content | `hagg.HaggFullAttachment.attachment_with_neighbor` | hagg.HaggFullAttachment.every_vertex_twin |
| hagg | `HaggFullAttachment.every_vertex_twin` | content | `hagg.HaggFullAttachment.every_vertex_twin` | hagg.HaggFullAttachment.pentagon_partition |
| hagg | `HaggFullAttachment.adjacency_of_twins` | bind-only | `none` | hagg.HaggFullAttachment.pentagon_partition |
| hagg | `HaggFullAttachment.pentagon_partition` | content | `hagg.HaggFullAttachment.pentagon_partition` | hagg.HaggkvistDense.pentagon_hom |
| hagg | `HaggBipartiteAlternative.pentagon_of_missing_cross` | content | `hagg.HaggBipartiteAlternative.pentagon_of_missing_cross` | hagg.HaggBipartiteAlternative.two_sides_of_no_pentagon |
| hagg | `HaggBipartiteAlternative.two_sides_of_no_pentagon` | content | `hagg.HaggBipartiteAlternative.two_sides_of_no_pentagon` | hagg.HaggkvistDense.pentagon_hom |
| hagg | `HaggBipartiteAlternative.pentagon_map_of_two_sides` | bind-only | `none` | hagg.HaggkvistDense.pentagon_hom |
| hagg | `PentagonImage.PathColor` | bind-only | `none` | hagg.PentagonImage.path_color_adj, hagg.PentagonImage.two_color_of_missing |
| hagg | `PentagonImage.path_color_adj` | bind-only | `none` | hagg.PentagonImage.two_color_of_missing |
| hagg | `PentagonImage.two_color_of_missing` | bind-only | `none` | hagg.PentagonImage.surjective_of_not_two_color |
| hagg | `PentagonImage.surjective_of_not_two_color` | bind-only | `none` | settlement.AEYLowerDense.no_small_dense, settlement.ExceptionalLower.no_order_59, settlement.ExceptionalLower.surjective |
| hagg | `HaggkvistDense.pentagon_hom` | content | `hagg.HaggkvistDense.pentagon_hom` | settlement.AEYLowerDense.no_small_dense, settlement.ExceptionalLower.no_order_59 |
| matching | `IsAlmostRegular` | bind-only | `none` | settlement.AEYInfimum.Z_eq_of_attainment, settlement.AEYLowerDense.lower_or_exception, settlement.AEYLowerDense.no_small_dense, settlement.ExceptionalLower.lower, settlement.ExceptionalLower.no_order_59, settlement.Z, settlement.result, upper.AEYUpperAttainment.attainment, matching.FactorCriticalOrder.almost_regular_order_eq |
| matching | `IsFactorCritical` | bind-only | `none` | settlement.AEYInfimum.Z_eq_of_attainment, settlement.AEYLowerDense.lower_or_exception, settlement.AEYLowerDense.no_small_dense, settlement.ExceptionalLower.lower, settlement.ExceptionalLower.no_order_59, settlement.ExceptionalNonbipartite.no_two_color, settlement.Z, settlement.result, upper.AEYUpperAttainment.attainment, matching.FactorCriticalNonbipartite.no_two_color, matching.FactorCriticalOrder.almost_regular_order_eq, matching.FactorCriticalOrder.order_eq, matching.FactorCriticalParity.odd_order |
| matching | `FactorCriticalParity.odd_order` | bind-only | `none` | settlement.AEYLowerDense.no_small_dense, matching.FactorCriticalOrder.order_eq |
| matching | `MatchingCountBridge.matchingCount_eq_cnt` | bind-only | `none` | matching.MatchingCountBridge.matchingCount_eq_zero_of_card_lt, matching.MatchingCountBridge.matchingCount_pos_of_matching, matching.MatchingCountBridge.matchingNumber_le |
| matching | `MatchingCountBridge.matchingCount_eq_zero_of_card_lt` | bind-only | `none` | matching.MatchingCountBridge.le_matchingNumber_of_pos, matching.MatchingCountBridge.matchingNumber_le |
| matching | `MatchingCountBridge.matchingNumber_le` | bind-only | `none` | matching.FactorCriticalOrder.order_eq |
| matching | `MatchingCountBridge.matchingCount_pos_of_matching` | bind-only | `none` | matching.FactorCriticalOrder.order_eq |
| matching | `MatchingCountBridge.matching_card_vertices` | bind-only | `none` | matching.FactorCriticalOrder.order_eq |
| matching | `MatchingCountBridge.le_matchingNumber_of_pos` | bind-only | `none` | matching.FactorCriticalOrder.order_eq |
| matching | `FactorCriticalOrder.order_eq` | bind-only | `none` | matching.FactorCriticalOrder.almost_regular_order_eq |
| matching | `FactorCriticalOrder.almost_regular_order_eq` | bind-only | `none` | settlement.AEYLowerDense.lower_or_exception, upper.AEYUpperAttainment.attainment |
| matching | `DenseBalancedHall.exists_equiv_of_omission_bound` | content | `matching.DenseBalancedHall.exists_equiv_of_omission_bound` | upper.PentagonPairMatching.exists_perfect_matching |
| matching | `PerfectMatchingBipartiteBalance.color_balance` | content | `matching.PerfectMatchingBipartiteBalance.color_balance` | settlement.ExceptionalNonbipartite.no_two_color, matching.FactorCriticalNonbipartite.no_two_color |
| matching | `PerfectMatchingBipartiteBalance.deleted_color_count` | bind-only | `none` | upper.AEYConstructionProperties.deleted_class_size, matching.FactorCriticalNonbipartite.no_two_color |
| matching | `FactorCriticalNonbipartite.no_two_color` | content | `matching.PerfectMatchingBipartiteBalance.color_balance` | settlement.AEYLowerDense.no_small_dense, settlement.ExceptionalLower.no_order_59, settlement.ExceptionalNonbipartite.no_two_color |
| obstruction | `OrderArithmetic.threshold_or_exception` | bind-only | `none` | settlement.AEYLowerDense.lower_or_exception |
| obstruction | `OrderArithmetic.class_size_floor` | bind-only | `none` | obstruction.PentagonSurjectiveLower.large_classes |
| obstruction | `OrderArithmetic.slack_regimes` | bind-only | `none` | obstruction.PentagonClassObstruction.no_small_class_data |
| obstruction | `PentagonSlack.MissingDegree` | bind-only | `none` | obstruction.PentagonClassObstruction.no_small_class_data, obstruction.PentagonSlack.slack_1_impossible, obstruction.PentagonSlack.slack_3_impossible |
| obstruction | `PentagonSlack.Feasible` | bind-only | `none` | obstruction.PentagonClassDegrees.almost_regular_feasible, obstruction.PentagonClassMass.feasible_class_mass, obstruction.PentagonClassObstruction.no_small_class_data, obstruction.PentagonDefectCounting.missing_degrees_feasible, obstruction.PentagonIncidence.feasible_of_symmetric_matrix, obstruction.PentagonSlack.incidence_inequalities, obstruction.PentagonSurjectiveLower.no_small_surjective_map |
| obstruction | `PentagonSlack.ConeCondition` | bind-only | `none` | obstruction.PentagonClassObstruction.no_small_class_data, obstruction.PentagonSlack.incidence_inequalities, obstruction.PentagonSlack.slack_1_impossible, obstruction.PentagonSlack.slack_3_impossible |
| obstruction | `PentagonSlack.incidence_inequalities` | bind-only | `none` | obstruction.PentagonClassObstruction.no_small_class_data |
| obstruction | `PentagonSlack.slack_1_impossible` | bind-only | `none` | obstruction.PentagonClassObstruction.no_small_class_data |
| obstruction | `PentagonSlack.slack_3_impossible` | bind-only | `none` | obstruction.PentagonClassObstruction.no_small_class_data |
| obstruction | `PentagonIncidence.feasible_of_symmetric_matrix` | bind-only | `none` | obstruction.PentagonClassMass.feasible_class_mass |
| obstruction | `PentagonClassMass.ClassMass` | bind-only | `none` | obstruction.PentagonClassMass.feasible_class_mass, obstruction.PentagonClassMass.mass_row, obstruction.PentagonClassMass.mass_symmetric |
| obstruction | `PentagonClassMass.mass_symmetric` | bind-only | `none` | obstruction.PentagonClassMass.feasible_class_mass |
| obstruction | `PentagonClassMass.mass_row` | bind-only | `none` | obstruction.PentagonClassMass.feasible_class_mass |
| obstruction | `PentagonClassMass.feasible_class_mass` | bind-only | `none` | obstruction.PentagonDefectCounting.missing_degrees_feasible |
| obstruction | `PentagonDefectCounting.cycle_five_adjacency` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, settlement.PentagonIndependentSubset.adjacent_counts_le_defect, upper.AEYUpperAbstract.factor_critical, upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small, obstruction.PentagonDefectCounting.defect_row, obstruction.PentagonDefectCounting.missing_degrees_feasible |
| obstruction | `PentagonDefectCounting.ClassSize` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, settlement.PentagonIndependentSubset.adjacent_counts_le_defect, upper.AEYConstructionProperties.class_size, upper.AEYConstructionProperties.deleted_class_size, upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.AEYUpperAbstract.class_omissions, upper.AEYUpperAbstract.factor_critical, upper.GraphOmissionBound.class_missing_le, obstruction.PentagonClassDegrees.almost_regular_feasible, obstruction.PentagonClassDegrees.class_deficit, obstruction.PentagonClassDegrees.degree_le_permitted, obstruction.PentagonClassDegrees.sum_class_sizes, obstruction.PentagonDefectCounting.defect_row, obstruction.PentagonDefectCounting.missing_degrees_feasible, obstruction.PentagonSurjectiveLower.large_classes, obstruction.PentagonSurjectiveLower.no_small_surjective_map |
| obstruction | `PentagonDefectCounting.DefectWeight` | bind-only | `none` | settlement.PentagonIndependentSubset.adjacent_counts_le_defect, upper.GraphOmissionBound.class_missing_le, obstruction.PentagonClassDegrees.degree_le_permitted, obstruction.PentagonDefectCounting.defect_row, obstruction.PentagonDefectCounting.defect_symmetric, obstruction.PentagonDefectCounting.missing_degrees_feasible |
| obstruction | `PentagonDefectCounting.defect_symmetric` | bind-only | `none` | obstruction.PentagonDefectCounting.missing_degrees_feasible |
| obstruction | `PentagonDefectCounting.defect_row` | bind-only | `none` | settlement.PentagonIndependentSubset.adjacent_counts_le_defect, upper.GraphOmissionBound.class_missing_le, obstruction.PentagonClassDegrees.degree_le_permitted, obstruction.PentagonDefectCounting.missing_degrees_feasible |
| obstruction | `PentagonDefectCounting.missing_degrees_feasible` | bind-only | `none` | obstruction.PentagonClassDegrees.almost_regular_feasible |
| obstruction | `PentagonClassDegrees.sum_class_sizes` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, obstruction.PentagonSurjectiveLower.large_classes, obstruction.PentagonSurjectiveLower.no_small_surjective_map |
| obstruction | `PentagonClassDegrees.degree_le_permitted` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, obstruction.PentagonSurjectiveLower.large_classes, obstruction.PentagonSurjectiveLower.no_small_surjective_map |
| obstruction | `PentagonClassDegrees.class_deficit` | bind-only | `none` | obstruction.PentagonClassDegrees.almost_regular_feasible |
| obstruction | `PentagonClassDegrees.almost_regular_feasible` | bind-only | `none` | obstruction.PentagonSurjectiveLower.no_small_surjective_map |
| obstruction | `PentagonClassObstruction.NeighborTotal` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, settlement.PentagonIndependentSubset.adjacent_counts_le_defect, obstruction.PentagonClassObstruction.no_small_class_data, obstruction.PentagonSurjectiveLower.large_classes, obstruction.PentagonSurjectiveLower.no_small_surjective_map, obstruction.PentagonSurjectiveLower.three_totals |
| obstruction | `PentagonClassObstruction.no_small_class_data` | bind-only | `none` | obstruction.PentagonSurjectiveLower.no_small_surjective_map |
| obstruction | `PentagonSurjectiveLower.three_totals` | bind-only | `none` | obstruction.PentagonSurjectiveLower.large_classes |
| obstruction | `PentagonSurjectiveLower.large_classes` | bind-only | `none` | obstruction.PentagonSurjectiveLower.no_small_surjective_map |
| obstruction | `PentagonSurjectiveLower.no_small_surjective_map` | content | `obstruction.PentagonSurjectiveLower.no_small_surjective_map` | settlement.AEYLowerDense.no_small_dense, settlement.ExceptionalLower.no_order_59 |
| upper | `PentagonPairSizes.BaseSize` | bind-only | `none` | upper.AEYConstructionProperties.class_size, upper.AEYConstructionProperties.deleted_class_size, upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.PentagonPairSizes.RemainingSize, upper.PentagonPairSizes.split_sizes |
| upper | `PentagonPairSizes.RemainingSize` | bind-only | `none` | upper.AEYConstructionProperties.deleted_class_size, upper.AEYUpperAbstract.factor_critical, upper.PentagonPairSizes.split_sizes |
| upper | `PentagonPairSizes.PairSize` | bind-only | `none` | upper.AEYUpperAbstract.factor_critical, upper.PentagonPairSizes.split_sizes |
| upper | `PentagonPairSizes.split_sizes` | bind-only | `none` | upper.AEYUpperAbstract.factor_critical |
| upper | `PairMatchingAssembly.exists_perfect_matching_of_pairs` | bind-only | `none` | upper.PentagonPairMatching.exists_perfect_matching |
| upper | `PentagonPairMatching.restricted_count_le` | bind-only | `none` | upper.PentagonPairMatching.exists_perfect_matching |
| upper | `PentagonPairMatching.exists_perfect_matching` | content | `upper.PentagonPairMatching.exists_perfect_matching` | upper.AEYUpperAbstract.factor_critical |
| upper | `AEYConstruction.BagSize` | bind-only | `none` | upper.AEYConstruction.B, upper.AEYConstruction.Deleted, upper.AEYConstruction.instDecidableAdjB, upper.AEYConstruction.instDecidableDeleted, upper.AEYConstruction.order, upper.AEYConstruction.triangle_free, upper.AEYConstructionProperties.class_map_adj, upper.AEYConstructionProperties.class_size, upper.AEYConstructionProperties.deleted_class_size, upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.AEYUpperAbstract.class_omissions, upper.AEYUpperAbstract.factor_critical, upper.AEYUpperAttainment.attainment, upper.ConstructionRows.degree_bag_sum, upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `AEYConstruction.BagClass` | bind-only | `none` | upper.AEYConstruction.B, upper.AEYConstruction.instDecidableAdjB, upper.AEYConstruction.triangle_free, upper.AEYConstructionProperties.class_map_adj, upper.AEYConstructionProperties.class_size, upper.AEYConstructionProperties.deleted_class_size, upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.AEYUpperAbstract.class_omissions, upper.AEYUpperAbstract.factor_critical, upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `AEYConstruction.PairedBags` | bind-only | `none` | upper.AEYConstruction.B, upper.AEYConstruction.Deleted, upper.AEYConstruction.instDecidableDeleted, upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `AEYConstruction.Deleted` | bind-only | `none` | upper.AEYConstruction.B, upper.AEYConstruction.instDecidableAdjB, upper.AEYConstruction.instDecidableDeleted, upper.AEYConstruction.triangle_free, upper.AEYConstructionProperties.class_map_adj, upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `AEYConstruction.instDecidableDeleted` | bind-only | `none` | upper.AEYConstruction.instDecidableAdjB |
| upper | `AEYConstruction.B` | bind-only | `none` | upper.AEYConstruction.instDecidableAdjB, upper.AEYConstruction.triangle_free, upper.AEYConstructionProperties.class_map_adj, upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.AEYUpperAbstract.class_omissions, upper.AEYUpperAbstract.factor_critical, upper.AEYUpperAttainment.attainment, upper.ConstructionRows.degree_bag_sum, upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `AEYConstruction.instDecidableAdjB` | bind-only | `none` | upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.AEYUpperAbstract.class_omissions, upper.AEYUpperAbstract.factor_critical, upper.AEYUpperAttainment.attainment, upper.ConstructionRows.degree_bag_sum, upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `AEYConstruction.order` | bind-only | `none` | upper.AEYUpperAttainment.attainment |
| upper | `AEYConstruction.triangle_free` | bind-only | `none` | upper.AEYUpperAttainment.attainment |
| upper | `ConstructionRows.count_equal` | bind-only | `none` | upper.ConstructionRows.count_unequal |
| upper | `ConstructionRows.count_unequal` | bind-only | `none` | upper.ConstructionRows.count_unequal_left |
| upper | `ConstructionRows.count_unequal_left` | bind-only | `none` | upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `ConstructionRows.degree_bag_sum` | bind-only | `none` | upper.ConstructionRows.degree_large, upper.ConstructionRows.degree_small |
| upper | `ConstructionRows.count_avoid_two` | bind-only | `none` | upper.ConstructionRows.count_forward_avoiding, upper.ConstructionRows.count_reverse_avoiding |
| upper | `ConstructionRows.count_forward_avoiding` | bind-only | `none` | upper.ConstructionRows.degree_large |
| upper | `ConstructionRows.count_reverse_avoiding` | bind-only | `none` | upper.ConstructionRows.degree_large |
| upper | `ConstructionRows.degree_small` | bind-only | `none` | upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.AEYUpperAttainment.attainment |
| upper | `ConstructionRows.degree_large` | bind-only | `none` | upper.AEYUpperAbstract.allowed_le_degree_add_two, upper.AEYUpperAttainment.attainment |
| upper | `AEYConstructionProperties.class_size` | bind-only | `none` | upper.AEYConstructionProperties.deleted_class_size, upper.AEYUpperAbstract.allowed_le_degree_add_two |
| upper | `AEYConstructionProperties.class_map_adj` | bind-only | `none` | upper.AEYUpperAbstract.class_omissions |
| upper | `AEYConstructionProperties.deleted_class_size` | bind-only | `none` | upper.AEYUpperAbstract.factor_critical |
| upper | `GraphOmissionBound.class_missing_le` | bind-only | `none` | upper.AEYUpperAbstract.class_omissions |
| upper | `GraphOmissionBound.deleted_class_missing_le` | bind-only | `none` | upper.AEYUpperAbstract.factor_critical |
| upper | `AEYUpperAbstract.allowed_le_degree_add_two` | bind-only | `none` | upper.AEYUpperAbstract.class_omissions |
| upper | `AEYUpperAbstract.class_omissions` | bind-only | `none` | upper.AEYUpperAbstract.factor_critical |
| upper | `AEYUpperAbstract.factor_critical` | content | `upper.PentagonPairMatching.exists_perfect_matching` | upper.AEYUpperAttainment.attainment |
| upper | `FactorCriticalTransport.perfect_matching_map` | bind-only | `none` | upper.FactorCriticalTransport.factor_critical |
| upper | `FactorCriticalTransport.factor_critical` | bind-only | `none` | upper.AEYUpperAttainment.attainment |
| upper | `AEYUpperAttainment.attainment` | content | `upper.AEYUpperAttainment.attainment` | settlement.result |
| settlement | `ExceptionalSupport.support_independent` | bind-only | `none` | settlement.ExceptionalHomExtension.extension |
| settlement | `ExceptionalSupport.independent_support_fits` | bind-only | `none` | settlement.ExceptionalHomExtension.extension |
| settlement | `Z` | bind-only | `none` | settlement.AEYInfimum.Z_eq_of_attainment, settlement.claim, settlement.result |
| settlement | `claim` | bind-only | `none` | settlement.result |
| settlement | `AEYLowerDense.relabel_edge` | bind-only | `none` | settlement.AEYLowerDense.no_small_dense, settlement.ExceptionalLower.no_order_59 |
| settlement | `AEYLowerDense.no_small_dense` | content | `obstruction.PentagonSurjectiveLower.no_small_surjective_map` | settlement.AEYLowerDense.lower_or_exception |
| settlement | `AEYLowerDense.lower_or_exception` | content | `obstruction.PentagonSurjectiveLower.no_small_surjective_map` | settlement.ExceptionalLower.lower |
| settlement | `VertexDeletionBridges.deleted_degree` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, settlement.ExceptionalLower.no_order_59, settlement.ExceptionalNonbipartite.no_two_color |
| settlement | `VertexDeletionBridges.neighbors_independent` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, settlement.ExceptionalNonbipartite.no_two_color |
| settlement | `VertexDeletionBridges.deleted_neighbor_count` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, settlement.ExceptionalNonbipartite.no_two_color |
| settlement | `VertexDeletionBridges.extend_hom` | bind-only | `none` | settlement.ExceptionalHomExtension.extension, settlement.ExceptionalNonbipartite.no_two_color |
| settlement | `IndependentBipartiteSupport.confined_to_one_color` | content | `settlement.IndependentBipartiteSupport.confined_to_one_color` | settlement.ExceptionalNonbipartite.no_two_color |
| settlement | `PentagonIndependentSubset.sum_counts` | bind-only | `none` | settlement.ExceptionalHomExtension.extension |
| settlement | `PentagonIndependentSubset.adjacent_counts_le_defect` | bind-only | `none` | settlement.ExceptionalHomExtension.extension |
| settlement | `ExceptionalHomExtension.extension` | content | `settlement.ExceptionalHomExtension.extension` | settlement.ExceptionalLower.no_order_59 |
| settlement | `ExceptionalNonbipartite.no_two_color` | content | `matching.PerfectMatchingBipartiteBalance.color_balance` | settlement.ExceptionalLower.no_order_59 |
| settlement | `ExceptionalLower.doubled_edge` | bind-only | `none` | settlement.ExceptionalLower.surjective |
| settlement | `ExceptionalLower.surjective` | bind-only | `none` | settlement.ExceptionalLower.no_order_59 |
| settlement | `ExceptionalLower.no_order_59` | content | `obstruction.PentagonSurjectiveLower.no_small_surjective_map` | settlement.ExceptionalLower.lower |
| settlement | `ExceptionalLower.lower` | content | `obstruction.PentagonSurjectiveLower.no_small_surjective_map` | settlement.AEYInfimum.Z_eq_of_attainment |
| settlement | `AEYInfimum.Z_eq_of_attainment` | content | `obstruction.PentagonSurjectiveLower.no_small_surjective_map` | settlement.result |
| settlement | `result` | content | `upper.AEYUpperAttainment.attainment` | settling result |
| dimer | `cnt` | bind-only | `none` | matching.MatchingCountBridge.matchingCount_eq_cnt, matching.MatchingCountBridge.matchingCount_eq_zero_of_card_lt, matching.MatchingCountBridge.matchingCount_pos_of_matching, matching.MatchingCountBridge.matchingNumber_le, dimer.result |
| dimer | `matchingsIn` | bind-only | `none` | matching.MatchingCountBridge.matchingCount_eq_cnt, matching.MatchingCountBridge.matchingCount_eq_zero_of_card_lt, matching.MatchingCountBridge.matchingCount_pos_of_matching, matching.MatchingCountBridge.matchingNumber_le, dimer.cnt, dimer.matchingsIn_eq_empty, dimer.result |
| dimer | `claim` | bind-only | `none` | dimer.result |
| dimer | `EdgeDisjoint` | bind-only | `none` | matching.MatchingCountBridge.matchingCount_eq_cnt, matching.MatchingCountBridge.matchingCount_pos_of_matching, matching.MatchingCountBridge.matchingNumber_le, dimer.matchingsIn, dimer.matchingsIn_eq_empty, dimer.result |
| dimer | `result` | content | `dimer.result` | settling result |
| dimer | `matchingsIn_eq_empty` | bind-only | `none` | matching.MatchingCountBridge.matchingCount_eq_zero_of_card_lt, dimer.result |
| dimer | `matchingNumber` | bind-only | `none` | settlement.AEYInfimum.Z_eq_of_attainment, settlement.AEYLowerDense.lower_or_exception, settlement.ExceptionalLower.lower, settlement.Z, settlement.result, upper.AEYUpperAttainment.attainment, matching.FactorCriticalOrder.almost_regular_order_eq, matching.FactorCriticalOrder.order_eq, matching.MatchingCountBridge.le_matchingNumber_of_pos, matching.MatchingCountBridge.matchingNumber_le, dimer.claim, dimer.result |
| dimer | `Biconnected` | bind-only | `none` | dimer.claim |
| dimer | `matchingCount` | bind-only | `none` | matching.MatchingCountBridge.le_matchingNumber_of_pos, matching.MatchingCountBridge.matchingCount_eq_cnt, matching.MatchingCountBridge.matchingCount_eq_zero_of_card_lt, matching.MatchingCountBridge.matchingCount_pos_of_matching, matching.MatchingCountBridge.matchingNumber_le, dimer.claim, dimer.matchingNumber, dimer.result |

## ASSUMED-UNVERIFIED

Literature completeness, the source's journal text, the original Häggkvist chapter, and every later paper outside the preregistration's inspected scope remain unverified. Bounded unsuccessful owner/bypass searches do not prove that no alternative proof exists. The total definition's even/small-degree and empty-carrier boundary is outside the proved statement. The registration gap is #20094.
