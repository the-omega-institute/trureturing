---
slug: movahedi-2025-diminished-sombor-energy-integer
bibkey: movahedi2025diminishedsombor
doi: 10.48550/arXiv.2508.06531
url: https://arxiv.org/abs/2508.06531v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.result
---

# Integer diminished Sombor energy of edgeless graphs

## Problem

F. Movahedi, *Diminished Sombor matrix, spectral radius, and energy of the
graphs*, arXiv:2508.06531v1, Section 5, page 19, states:

> Conjecture 5.1 There does not exist a graph whose diminished Sombor energy is an integer value.

For vertex degrees $d_i$, the real symmetric matrix has entry
$\sqrt{d_i^2+d_j^2}/(d_i+d_j)$ on an edge and zero otherwise.
Its energy is the sum of the absolute values of all eigenvalues, counted
with multiplicity. The conjecture places no edge or connectedness
restriction on the graph. Corollary 4.3, page 17, explicitly includes the
edgeless graph as an equality case. Issue #13380 preregisters the positive
order, finite simple graph statement and its edgeless counterexample.

## Motivation

`D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.result`
refutes the literal all-graphs nonintegrality statement. The one-vertex
edgeless graph has energy zero, an integer.

## Gap

Tier 1: a named conjecture in the source's closing section. The
preregistration records MathDB #369710 with no posted solutions, arXiv v1,
and no settlement in its repository searches. These literature readings
are source-reported; absence within that scope does not establish
exhaustive coverage or priority. Nonintegrality for graphs with at least
one edge is a separate unbounded question.

## Route

For every edgeless graph, adjacency is false at every ordered vertex pair,
so the non-edge branch gives the zero matrix without evaluating any
degree quotient. Mathlib's
`Matrix.IsHermitian.eigenvalues_eq_zero_iff` gives the identically zero
eigenvalue function. Its absolute-value sum is zero. The integer zero at
order one contradicts the universal `claim`.

## Falsifier

A source restriction requiring an edge would exclude this witness. The
quoted conjecture has no such restriction, and its own energy bound
includes edgeless graphs. The witness has positive order, so no empty
vertex domain is needed. Real division at zero does not cause the
refutation: the non-edge branch is zero directly.

## Evidence

The Lean source is
`D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.lean`.
Its explicit source declarations are `diminishedSomborMatrix`,
`diminishedSomborEnergy`, `claim` and `result : ¬ claim`.
Auxiliary propositions are local to `result`; `energy_zero (n : ℕ)`
establishes the zero-energy statement for every order within that proof.
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

## Triage

Tier 1; resolution `Refuted`; `proof_shape: bind-only`;
`escape_witness: none`; `admission_basis: open-problem-resolution (#13380; Refuted)`.
Utility is `kind=certified-instance; basis=refutes`, with the closed
source `claim` and its designated `result`.
Information-escape registration is paused under CLAUDE.md section 3.9.

### What the settlement shows

**Proved in this module:** every edgeless finite graph has zero matrix,
zero eigenvalues and zero energy, by the local `matrix_zero` and
`energy_zero` proofs for arbitrary order. The public `result` uses order
one to refute DSE. The failure mechanism is the omitted edge hypothesis:
non-edge entries are zero even when both endpoint degrees vanish.
The edgeless equality case of Corollary 4.3 survives this witness.

**Computed, not proved:** the NetworkX graph atlas scan checks every
isomorphism class with at least one edge and at most seven vertices.
With absolute tolerance $10^{-9}$, none of 1,245 energies lies within
that tolerance of an integer. Tested counts for orders 1 through 7 are
0, 1, 3, 10, 33, 155 and 1,043. The minimum distance to the nearest integer
is 0.0005173861790490619, at atlas index 509, graph6 `FjsAG`, order 7,
9 edges, energy 6.999482613820951, nearest integer 7.
This is a floating-point observation, not a certificate of nonintegrality.

Command: `python3 /Users/auric/.sshx/f36bdf0e5e16afdc328e94a3/attempt-1/dse_atlas.py`.
Exit code: 0. Script SHA-256:
`cf08c45dd0bdbb126cfc21e8aca74f26ebda304f54757f390f27a86ca5b01524`.
Environment: Python 3.13.2, NetworkX 3.4.2, NumPy 2.2.5.
The complete experimental program is below; its bytes include a final newline.

```python
import json
import platform
import networkx as nx
import numpy as np

tolerance = 1e-9
rows = {n: {"n": n, "tested": 0, "near_integer": 0} for n in range(1, 8)}
nearest = None
for index, graph in enumerate(nx.graph_atlas_g()):
    n = len(graph)
    if not 1 <= n <= 7 or graph.number_of_edges() == 0:
        continue
    vertices = list(graph)
    degrees = dict(graph.degree())
    matrix = np.zeros((n, n), dtype=np.float64)
    for i, u in enumerate(vertices):
        for j, v in enumerate(vertices):
            if graph.has_edge(u, v):
                du, dv = degrees[u], degrees[v]
                matrix[i, j] = np.sqrt(du * du + dv * dv) / (du + dv)
    assert np.array_equal(matrix, matrix.T)
    energy = float(np.abs(np.linalg.eigvalsh(matrix)).sum())
    assert np.isfinite(energy)
    gap = abs(energy - round(energy))
    rows[n]["tested"] += 1
    rows[n]["near_integer"] += int(gap <= tolerance)
    if nearest is None or gap < nearest["gap"]:
        nearest = dict(atlas_index=index, n=n, edges=graph.number_of_edges(),
                       graph6=nx.to_graph6_bytes(graph, header=False).decode().strip(),
                       energy=energy, nearest_integer=round(energy), gap=gap)
result = dict(python=platform.python_version(), networkx=nx.__version__, numpy=np.__version__,
              tolerance=tolerance, rows=list(rows.values()),
              tested=sum(row["tested"] for row in rows.values()),
              near_integer=sum(row["near_integer"] for row in rows.values()), nearest=nearest)
print(json.dumps(result, indent=2))
assert result["tested"] > 0 and result["near_integer"] == 0
```

**Open:** DSE restricted to finite simple graphs with at least one edge,
of arbitrary order. The bounded numerical scan does not prove this
restriction, including exact nonintegrality in the tested range.

**Proved in prose from the source, not formalized:** for a connected
$k$-regular graph with $k>0$, Theorem 3.1 gives
$M_{DS}(G)=A(G)/\sqrt{2}$ and scales every adjacency eigenvalue by
$1/\sqrt{2}$. Hence $E_{DSO}(G)=E(G)/\sqrt{2}$, so integer diminished
Sombor energy would require $E(G)\in\sqrt{2}\,\mathbb Z$.
For $k=0$ a connected nonempty graph is the singleton and both energies
are zero; no division by $k$ is required in that case.
This source-derived relation is outside the delivered Lean theorem;
whether it excludes all positive-degree regular graphs remains open here.

**Source consequence:** Conjecture 5.1 occurs after the paper's theorems
and corollaries, with no earlier invocation of this conjecture. The
refutation supplies no contradiction to those independent results and
does not verify their proofs. The source's two subsequent questions about
edge/vertex removal and operations on pairs of graphs remain open here.
MathDB #351674 (Sombor energy) and #362891 (elliptic Sombor energy) concern
different matrices and are not settled by this module.

## ASSUMED-UNVERIFIED

The preregistration's external literature-status readings are
source-reported. Exhaustive literature coverage and priority are not
established. The atlas calculation uses floating-point eigenvalues and
an absolute tolerance. The regular-graph consequence is a source-derived
prose proof, not kernel evidence in this module.
