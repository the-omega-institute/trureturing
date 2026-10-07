---
slug: song-dalfo-fiol-zhang-2026-token-graph-laplacian-radius-refutation
bibkey: song2026tokenradius
doi: 10.48550/arXiv.2610.00500
url: https://arxiv.org/abs/2610.00500v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.result
---

# A disconnected counterexample to the token-radius conjecture

## Problem

X. Song, C. Dalfó, M. À. Fiol and S. Zhang, *The Algebraic Connectivity and
Laplacian Spectral Radius of Token Graphs*, arXiv:2610.00500v1, section 1,
page 4, state:

> Conjecture 1.1. Let G be a graph of order n(≥ 4), the equality
> ρ(F_k(G)) = ρ(G) holds for all k with 2 ≤ k ≤ ⌊n/2⌋ if and only if G ≅ S_n.

Here the token vertices are k-subsets, adjacency means that their symmetric
difference is an edge of G, and ρ is the largest Laplacian eigenvalue.
The literal statement has no connectedness hypothesis. Issue #12457
preregisters this reading and the counterexample K₂ ⊔ 2K₁.

## Motivation

The equality would characterize stars using the spectra of all token graphs
in the specified range. The declaration
`D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.result`
refutes this characterization over all finite simple graphs.

## Gap

The preregistration classifies the problem as Tier 1: a newly published,
explicitly named conjecture. Its literature reading found no settlement in
the paper, MathDB, or the searched repository scope. The current arXiv record
lists only v1; Conjecture 1.1 remains in that version. This is
`not-found-in-searched-scope`, not a claim of exhaustive literature coverage
or priority. The connected version is a separate question.

## Route

Take the graph on Fin 4 with only edge {0,1}. Its two-token vertices are
01, 02, 03, 12, 13, 23, and its two edges are 02–12 and 03–13.
Both nonzero real Laplacians satisfy L² = 2L. For every eigenvector this
implies λ(λ−2) = 0, so all eigenvalues are 0 or 2. The Hermitian spectral
theorem and nonzero matrix exclude all eigenvalues being zero. Hence both
largest eigenvalues are 2. At n = 4 the range contains only k = 2.
The original graph has one edge; S₄ has three. Isomorphisms preserve edge
counts, so the asserted equivalence fails.

The source uses Mathlib's `Set.powersetCard`, `SimpleGraph.lapMatrix`,
`SimpleGraph.starGraph` and Hermitian eigenvalues directly. All supporting
calculations are local to the one settling theorem.

## Falsifier

A source hypothesis requiring connectedness would exclude this witness.
No such hypothesis occurs in the quoted conjecture or the encoded `claim`.
The empty-carrier value of `rho` is irrelevant: n ≥ 4 and every k in the
range has at least one k-subset. An isomorphism to S₄ would contradict the
kernel-computed edge counts 1 and 3.

## Evidence

The Lean source is
`D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean`.
Its public surface is `tokenGraph`, `instTokenGraphDecidableAdj`, `rho`,
`claim`, and `result : ¬ claim`. The graph carrier, finite instances,
Laplacian and star reuse pinned Mathlib. The sole theorem uses the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`.

The following independent numerical experiment enumerates every isomorphism
class of simple graphs of orders 4–7 with at least one edge, using NetworkX's
graph atlas. Run the code with `python3`; Python 3.13.2, NetworkX 3.4.2 and
NumPy 2.2.5 produce the table below. Equality is tested with absolute tolerance
10⁻⁸. This is a floating-point computation, not a Lean certificate.

```python
import itertools, json, platform
import networkx as nx
import numpy as np

def lap_radius(g):
    a = nx.to_numpy_array(g, nodelist=list(g), dtype=float)
    return float(np.linalg.eigvalsh(np.diag(a.sum(axis=1)) - a)[-1])

def token_graph(g, k):
    sets = [frozenset(s) for s in itertools.combinations(g.nodes, k)]
    t = nx.Graph()
    t.add_nodes_from(sets)
    for s, u in itertools.combinations(sets, 2):
        d = s ^ u
        if len(d) == 2 and g.has_edge(*d):
            t.add_edge(s, u)
    return t

rows = []
for n in range(4, 8):
    graphs = [g for g in nx.graph_atlas_g() if len(g) == n and g.number_of_edges() > 0]
    matches = []
    connected_nonstars = []
    min_failed_gap = float('inf')
    max_match_gap = 0.0
    for g in graphs:
        gaps = [abs(lap_radius(token_graph(g,k)) - lap_radius(g)) for k in range(2,n//2+1)]
        star = nx.is_isomorphic(g, nx.star_graph(n-1))
        if max(gaps) < 1e-8:
            matches.append((nx.is_connected(g), star, nx.to_graph6_bytes(g, header=False).decode().strip()))
            max_match_gap = max(max_match_gap,max(gaps))
            if nx.is_connected(g) and not star:
                connected_nonstars.append(matches[-1][2])
        else:
            min_failed_gap = min(min_failed_gap,max(gaps))
    rows.append(dict(n=n, graphs=len(graphs), connected_graphs=sum(nx.is_connected(g) for g in graphs), equality_matches=len(matches), stars=sum(x[1] for x in matches), disconnected=sum(not x[0] for x in matches), connected_nonstars=connected_nonstars, max_match_gap=max_match_gap, min_failed_max_gap=min_failed_gap, graph6=[x[2] for x in matches]))
print(json.dumps(dict(python=platform.python_version(),networkx=nx.__version__,numpy=np.__version__,tolerance=1e-8,rows=rows),indent=2))
```

| n | graphs with an edge | connected graphs | equality matches | stars | disconnected matches |
| --- | --- | --- | --- | --- | --- |
| 4 | 10 | 6 | 4 | 1 | 3 |
| 5 | 33 | 21 | 5 | 1 | 4 |
| 6 | 155 | 112 | 6 | 1 | 5 |
| 7 | 1043 | 853 | 7 | 1 | 6 |

There are 1241 tested graphs and 22 matches: four stars and eighteen
disconnected graphs. Among matches the largest absolute radius difference
is 2.665×10⁻¹⁵; among nonmatches the smallest maximum difference over k
is greater than 0.999999999999998. Graphs with no edges also satisfy equality
and are explicitly excluded from this numerical table.

## Triage

Tier 1; `theorem`; resolution `refuted`. The theorem's `proof_shape` is
`bind-only`: finite matrix evaluation, existing spectral identities,
algebraic normalization, finite maxima and isomorphism invariance suffice.
Its `escape_witness` is `none`. Admission basis is
`open-problem-resolution`, preregistration #12457; utility is
`kind=certified-instance; basis=refutes`, with the closed `claim` and `result`.
Information-escape registration is paused under CLAUDE.md section 3.9.

### What the settlement shows

**Proved in this module:** K₂ ⊔ 2K₁ satisfies the spectral equalities at every
k in the n = 4 range, but is not a star. Token moves conserve the choices
of occupied isolated vertices. For this witness the token graph splits into
two single-edge blocks and two isolated vertices, each nonzero block having
largest Laplacian eigenvalue 2. The absence of connectedness permits this
failure mechanism. Disconnectedness alone does not imply equality for an
arbitrary graph: different nontrivial components can contribute jointly.

**Proved in prose, not formalized:** for every n ≥ 4 let
G = K₂ ⊔ (n−2)K₁. For 1 ≤ k ≤ n−1, every token configuration with exactly
one occupied endpoint of the single edge is paired with the configuration
obtained by exchanging that endpoint. The occupied isolated vertices are
unchanged. Thus F_k(G) is a matching with binomial(n−2,k−1) edges plus
binomial(n−2,k−2) + binomial(n−2,k) isolated vertices, with out-of-range
binomial coefficients zero. The matching is nonempty, so ρ(F_k(G)) = 2 = ρ(G).
G has one edge whereas S_n has n−1 ≥ 3 edges. This gives the same
counterexample for every n ≥ 4 without adding a companion Lean theorem.

**Computed:** the atlas scan supports the connected version for
4 ≤ n ≤ 7: every connected match is a star. It gives numerical evidence
within the stated tolerance, not an exact finite-case proof.

**Open:** Conjecture 1.1 restricted to connected finite simple graphs of
arbitrary order. A connected counterexample or proof is outside this
settlement; the finite scan cannot settle the unbounded claim.

**Source consequence:** no later proof in arXiv:2610.00500v1 explicitly
invokes Conjecture 1.1. The independent statements with connectedness
hypotheses, including the tree characterization (Theorem 4.4) and connected
regular-graph strictness (Theorem 4.6), are not contradicted by this
witness. Their proofs are not verified by this module. The conjectured
all-graphs characterization requires replacement or an additional
hypothesis; the connected formulation remains the nearest open candidate.

## ASSUMED-UNVERIFIED

The preregistration's MathDB and prior-literature reading is source-reported.
No exhaustive worldwide search or priority is established. The atlas result
uses floating-point eigenvalues; its tolerance test is not formal equality.
The general-family argument is prose evidence, not kernel evidence.
