---
slug: op-alr2606sparse
bibkey: aceskalortripperger2026ornaments
doi: 10.48550/arXiv.2606.16001
url: https://arxiv.org/abs/2606.16001v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.result
---

# The fourteen-vertex DDMOG edge bound

## Problem

Aceska, Lort and Ripperger conjecture in the conclusion that the DDMOG in Figure 6 is the sparsest connected DDMOG on fourteen vertices. Remark 2 gives that construction $24$ edges. The fixed-order claim quantifies over all oriented digraphs with fourteen vertices and all difference distance magic labelings. It asserts at least $24$ edges whenever the underlying graph is connected. [Source, arXiv:2606.16001v3](https://arxiv.org/abs/2606.16001v3) · [Preregistration #25620](https://github.com/the-omega-institute/trureturing/issues/25620)

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Fourteen vertices and all oriented graphs | `claim` quantifies over `Digraph (Fin 14)` and assumes asymmetric adjacency. Asymmetry excludes loops and opposite arcs. |
| Connected underlying graph | `claim` takes `SimpleGraph.fromRel` on the disjunction of the two arc directions and requires `Connected`. The proof uses `Digraph.toSimpleGraphInclusive` through `underlying_eq`. |
| Bijection onto $\{1,\ldots,14\}$ | `claim` quantifies over integer label functions. `IsConsecutiveLabeling` requires `Set.BijOn` from the full finite vertex set onto the closed integer interval. |
| All weights equal a common natural $k$ | `IsDDMLabeling` retains the existential natural constant and one equality per vertex. `weight` subtracts the outgoing label sum from the incoming label sum. Both sums range over the vertex set and use zero outside the respective neighborhood. |
| At least $24$ edges | `edgeCount` counts adjacent ordered pairs. Asymmetry makes their count equal to the underlying edge count. `claim` compares that count with $24$. |
| Indexing and integer coercions | `Fin 14` indexes vertices from $0$. Its vertex at index $i$ receives label $i+1$ in the certificate. The interval endpoints and common weight are compared in the integers. |

## Motivation

The designated settling declaration is `D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.result`. It proves the negation of `claim`. The module has generality `I` and supplies a certified instance.

## Gap

The literature screen in #25620 found no settlement of this fixed-order claim in the sources it could read. It records the related arXiv work and the degree bound of Altman et al. [Literature screen](https://github.com/the-omega-institute/trureturing/issues/25620)

## Route

The construction chooses $23$ oriented edges and uses the consecutive labels $1$ through $14$. At each vertex the incoming labels add to the same integer as the outgoing labels. The underlying spanning tree connects all fourteen vertices. The label bijection, orientation, connectivity, weight equalities and cardinality apply to the same graph.

## Falsifier

A connected orientation on fourteen vertices with a DDM labeling and fewer than $24$ edges contradicts the claim. The certificate has $23$ edges and common weight $0$.

## Evidence

The module's private declarations `labels_consecutive`, `witness_oriented`, `witness_connected`, `witness_weights`, `witness_ddm` and `witness_edges` prove the corresponding properties of the explicit graph. `result` combines them to refute the stated bound.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The exact integer checker `check.py` has SHA-256 `b95354ce34512679e05903466fceca13e2a2184af52a25e008a263f33079f147`. The command `python3 check.py` exits $0$ and checks the Figure 6 and counterexample orientations, their edge counts, their underlying connectivity and all $14$ weights in each graph. [Pinned experiment at 2842b0dd76520525eb1ae93b26d3300b57c30a35](https://github.com/the-omega-institute/trureturing-experiments/tree/2842b0dd76520525eb1ae93b26d3300b57c30a35/docs/reports/aceska-lort-ripperger-sparsest-ddmog14)

A local structure check takes the counterexample arcs from that same pinned `check.py`. The command `python3 check-structure.py check.py` exits $0$. The supplementary script has SHA-256 `eb2dd65ba3f8036cfa15d09ffa0568036af0f03a4867c6b36041d87ef36397b2` and has local evidence status.

## Triage

### What the settlement shows

1. **Proved in Lean.** `result` refutes the connected fourteen-vertex $24$-edge lower bound. `witness_weights` establishes weight $0$ at every vertex of the nominated $23$-edge orientation and `labels_consecutive` verifies its consecutive labels. Its local additive identities balance at every vertex while the arcs still connect the graph. This refutes the asserted edge minimality of Figure 6.
2. **Computed.** The pinned integer checker verifies that Figure 6 itself is a connected fourteen-vertex orientation with $24$ edges and all weights zero under its displayed labeling. It still supplies the paper's existence example.
3. **Computed.** The structure check finds one strongly connected component on all fourteen vertices of the $23$-edge witness. In label order its incident degrees are $(4,4,3,4,3,3,3,3,3,4,3,3,3,3)$.
4. **Open.** The exact minimum at order fourteen belongs to $\{21,22,23\}$. The lower endpoint follows from Altman et al., Property 1, since summing the minimum incident degree $3$ over $14$ vertices gives $2|E|\ge42$. The upper endpoint comes from the Lean certificate. Existence at $21$ and $22$ edges remains open in the checked scope. [Altman et al., 2024](https://doi.org/10.1007/s40687-024-00482-7)
5. **Open.** The general sparsest-edge formula, a family extending this witness and the separate sparsest $s$-node ornament questions remain open in the checked scope.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration records incomplete citing-work, MathOverflow, MathDB, broad Zenodo and full-text coverage. [Preregistration #25620](https://github.com/the-omega-institute/trureturing/issues/25620)
