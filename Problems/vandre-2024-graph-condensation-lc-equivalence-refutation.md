---
slug: vandre-2024-graph-condensation-lc-equivalence-refutation
bibkey: vandre2024marginals
doi: 10.48550/arXiv.2406.09956
url: https://arxiv.org/abs/2406.09956v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.result
---

# Condensation need not preserve LC-equivalence

## Problem

Vandré, de Jong, Hahn, Burchardt, Gühne and Pappa, *Distinguishing Graph
States by the Properties of Their Marginals*, arXiv:2406.09956v2,
Section V, Conjecture 16, p. 13:

> Given two graphs G and G′ and a condensation set C such that each node in C is connected to at most one node in the neighborhood in V \ C. If G and G′ are LC-equivalent, it follows that G_c and G′_c are LC-equivalent.

The paper considers simple connected graphs. Definition 13 (p. 12) replaces
C by one fresh vertex c, retains edges between vertices outside C, and joins
c to an outside vertex i exactly when some vertex of C is adjacent to i.
Local complementation (Definition 4, pp. 4–5) complements adjacency among
the selected vertex's neighbours. The correspondence with local Clifford
operations of the associated graph states is stated on p. 5 and attributed
to Van den Nest, Dehaene and De Moor (2004), DOI
10.1103/PhysRevA.69.022316. The formal statement uses finite labelled graphs
and finite sequences of these local complementations.

The complete quantified claim is:

```lean
∀ (V : Type) [Fintype V] [DecidableEq V] (G H : SimpleGraph V) (C : Finset V),
  G.Connected → H.Connected →
  (∀ s ∈ C, (Finset.univ.filter fun i => i ∉ C ∧ G.Adj s i).card ≤ 1) →
  (∀ s ∈ C, (Finset.univ.filter fun i => i ∉ C ∧ H.Adj s i).card ≤ 1) →
  LCEquivalent G H → LCEquivalent (condense G C) (condense H C)
```

Both graphs must satisfy the outside-neighbour bound. This is the more
restrictive reading of the premise, so a counterexample satisfying both
bounds also refutes a reading requiring the bound on only one graph.

## Motivation

Issue #11473 preregisters the verbatim published assertion, Tier 1
classification, full quantified reading and the six-vertex counterexample.
The independent question is exactly Conjecture 16, not a positive finite
instance of a known theorem.

## Gap

The inspected v2 retains the conjecture. Appendix C's counterexamples
address broader condensation rules with several outside neighbours per
vertex of C. The literature scope in #11473 includes the cited arXiv works,
INSPIRE references, and J. de Jong's thesis (DOI
10.14279/depositonce-23579); no settlement was found in that scope. One
Huang–Chen journal full text was inaccessible and remains
ASSUMED-UNVERIFIED. No priority or exhaustive literature claim is made.

## Route

Take V = Fin 6 and C = {0, 1, 2}. The first graph has edges
{01, 02, 05, 14, 23}; the second has edges {05, 14, 23, 35, 45}.
Both are connected. Each of 0, 1 and 2 has exactly one neighbour outside C
in each graph. Local complementation at 0, 1, 2, 3, 4, 5, in that order,
maps the first graph to the second.

On the common condensed vertex type Option {v : Fin 6 // v ∉ C}, none is
the fresh vertex and some 3, some 4, some 5 are the outside vertices.
The first condensation is a star with centre none. The second has the five
edges {c3, c4, c5, 35, 45}, a diamond.

The complete graph and the stars form a family invariant under local
complementation: complementation at a star's centre produces the complete
graph, at a different vertex preserves the star, and at a vertex of the
complete graph produces the star centred there. Induction over the entire
finite sequence keeps every graph reachable from the first condensation in
this family. The second condensation is neither complete nor a star,
as concrete adjacency comparisons establish. Thus the condensed graphs
are not LC-equivalent despite satisfying all the conjecture's hypotheses.

## Falsifier

An incorrect adjacency table, failure of connectivity or either
outside-neighbour bound, or a local-complementation sequence from the
condensed star to the diamond would invalidate the counterexample. The
kernel proof verifies the finite hypotheses and excludes every such
sequence by the invariant-family induction.

## Evidence

The module's public definitions are condense, LCEquivalent and claim;
its only public theorem is result : ¬ claim. The graph constructors and
finite decidability instances are private data; there are no private
named theorems or lemma wrappers. The closure and sequence induction are
inline in result.

proof_shape: result: content. The escape is form (2): the live invariant
induction and adjacency exclusions produce the refutation itself.
admission_basis: open-problem-resolution (#11473; Refuted).
utility: certified-instance, refutes the independently preregistered claim.

The imported frozen definitions lc and lcSeq come from
D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph, whose module
statement_id is
sha256:81981077a3cd56f484109eb63008d9318f6a36c1c70e0df494f9f09515aef166.
Their declaration statement_ids are respectively
sha256:9f294d833f9432cb07f2efb1392793f29502edb5cbbaf03040dfb51b165eae79
and sha256:cf3d985ac05293bf2cacb55e059beb758fb7c5ab957b6091dac7c4bf62249932.
The imported module's settling theorem is not applied.

result uses only propext, Classical.choice and Quot.sound.
The Scribe theorem node binds this dossier with
OpenProblemResolutionClaim(Refuted).

## Triage

Tier 1 external named conjecture, preregistered in #11473 before Lean.
The dossier triage is theorem and the resolution is Refuted. The only
public theorem is result, with proof_shape content and admission_basis
open-problem-resolution; its certified-instance utility refutes claim.

### What the settlement shows

- The outside-neighbour bound on both endpoints and connectivity do not
  suffice: the explicit LC-equivalent pair condenses to LC-inequivalent
  graphs. Consequently, using Conjecture 16's rule to infer inequivalence
  of the original graphs from inequivalence of their condensations gives
  a false certificate on this pair.
  [proved: D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.result]

- Condensation merges three distinct attachments, 0–5, 1–4 and 2–3,
  into one vertex while retaining the outside edges. Along the witness's
  LC sequence, the outside degrees of (0,1,2), including the initial state,
  are (1,1,1), (1,2,2), (1,2,2), (1,2,2), (1,3,1), (3,1,1), (1,1,1).
  Thus the endpoint bound does not control the intervening operations.
  Both endpoints are connected with five edges, so restricting both graphs
  to trees does not repair the rule; the induced graphs on C have two and
  zero edges, respectively.
  [computed: run the inline Python 3 reproduction below; output key `witness` and its exact output below]

- Allowing a relabelling of the condensed graphs does not repair this
  witness. Breadth-first enumeration of the four-vertex star's labelled
  LC orbit gives five graphs with edge counts (3,3,3,3,6); the diamond's
  orbit has eleven graphs with counts (3,3,3,3,4,4,4,4,4,5,5).
  None of the diamond's 24 vertex permutations lies in the star orbit.
  [computed: run the inline Python 3 reproduction below; output key `orbits` and its exact output below]

- A restricted single-step rule survives exhaustive six-vertex checking
  for C={0,1,2}, without imposing connectivity. Among all 4096 graphs
  satisfying the initial outside-degree bound, all 12288 complementations
  at a vertex of C leave the condensation unchanged. For an outside
  pivot, all 6960 steps whose final graph also satisfies the bound commute
  with condensation, using the corresponding outside pivot afterwards.
  [computed: run the inline Python 3 reproduction below; output key `restricted_steps` and its exact output below]

- The general repair requiring an LC sequence whose every intermediate
  graph satisfies the outside-neighbour bound remains unproved here.
  The single-step computation supports this candidate on six vertices;
  neither the computation nor the refutation establishes it for arbitrary
  finite vertex sets or shows that such a sequence must exist whenever
  the bound holds at the endpoints.
  [open]

- Singleton condensation survives a broader finite check without any
  degree or connectivity assumption. For every labelled simple graph on
  one through five vertices, every singleton C and every LC pivot,
  condensation commutes with LC after renaming C's vertex to the fresh
  vertex. This checks the one-step identity only in the stated range.
  [computed: run the inline Python 3 reproduction below; output key `singleton_steps` and its exact output below]

- The witness does not meet the paper's established condensation
  hypotheses. In both endpoints its C-to-(3,4,5) adjacency matrix is
  ((0,0,1),(0,1,0),(1,0,0)), of rank 3 over GF(2). Equation (21) therefore
  gives d_C=3−3=0, whereas Lemma 15 requires d_C=|C|−1=2;
  Lemma 14 additionally requires |C|=2. This witness does not refute
  either lemma or the Section VI complexity calculation explicitly based
  on Lemma 15. It excludes substituting Conjecture 16's degree condition
  for those hypotheses, including when condensation is iterated.
  [computed: run the inline Python 3 reproduction below; output key `cut_ranks` and its exact output below]

### Executable reproduction

Run this command outside the repository with Python 3. Its five JSON records
reproduce all five computed claims above.

```sh
python3 - <<'PY'
from itertools import combinations, permutations, product
import json


def edge(a, b):
    return tuple(sorted((a, b)))


def lc(E, v):
    N = [b if a == v else a for a, b in E if v in (a, b)]
    return E ^ {edge(a, b) for a, b in combinations(N, 2)}


def condense(E, C):
    def renamed(v):
        return -1 if v in C else v
    return {edge(renamed(a), renamed(b)) for a, b in E
            if renamed(a) != renamed(b)}


def bound(E, C):
    return all(sum(s in e and not set(e) <= C for e in E) <= 1 for s in C)


def connected(E, n):
    seen = {0}
    while True:
        new = seen | {v for e in E if set(e) & seen for v in e}
        if new == seen:
            return len(seen) == n
        seen = new


def orbit(E, vertices):
    seen, todo = {frozenset(E)}, [E]
    while todo:
        for v in vertices:
            F = frozenset(lc(todo[-1], v))
            if F not in seen:
                seen.add(F)
                todo.insert(0, set(F))
        todo.pop()
    return seen


def subsets(items):
    for mask in range(1 << len(items)):
        yield {e for i, e in enumerate(items) if mask >> i & 1}


C = {0, 1, 2}
G = {(0, 1), (0, 2), (0, 5), (1, 4), (2, 3)}
H = {(0, 5), (1, 4), (2, 3), (3, 5), (4, 5)}
F, degrees = G, []
for v in [None, 0, 1, 2, 3, 4, 5]:
    if v is not None:
        F = lc(F, v)
    degrees.append([sum(s in e and not set(e) <= C for e in F) for s in sorted(C)])
assert F == H
print(json.dumps({'witness': {'outside_degrees': degrees,
    'connected': [connected(E, 6) for E in (G, H)],
    'edge_counts': [len(G), len(H)],
    'internal_C_edges': [sum(set(e) <= C for e in E) for E in (G, H)]}}))

star, diamond = condense(G, C), condense(H, C)
vertices = [-1, 3, 4, 5]
O, D = orbit(star, vertices), orbit(diamond, vertices)
hits = 0
for p in permutations(vertices):
    rename = dict(zip(vertices, p))
    hits += frozenset(edge(rename[a], rename[b]) for a, b in diamond) in O
print(json.dumps({'orbits': {'star_size': len(O), 'diamond_size': len(D),
    'relabelled_diamond_hits': hits,
    'star_edge_counts': sorted(map(len, O)), 'diamond_edge_counts': sorted(map(len, D))}}))

internal = list(combinations(range(3), 2)) + list(combinations(range(3, 6), 2))
graphs = inside = outside = inside_bad = outside_bad = 0
for I in subsets(internal):
    for attachments in product([None, 3, 4, 5], repeat=3):
        E = I | {edge(s, t) for s, t in enumerate(attachments) if t is not None}
        assert bound(E, C)
        graphs += 1
        for v in range(6):
            F = lc(E, v)
            if v in C:
                inside += 1
                inside_bad += condense(F, C) != condense(E, C)
            elif bound(F, C):
                outside += 1
                outside_bad += condense(F, C) != lc(condense(E, C), v)
print(json.dumps({'restricted_steps': {'graphs': graphs, 'inside_steps': inside,
    'inside_mismatches': inside_bad, 'eligible_outside_steps': outside,
    'outside_mismatches': outside_bad}}))

graphs = pairs = steps = bad = 0
for n in range(1, 6):
    for E in subsets(list(combinations(range(n), 2))):
        graphs += 1
        for c in range(n):
            pairs += 1
            for v in range(n):
                steps += 1
                bad += condense(lc(E, v), {c}) != lc(condense(E, {c}), -1 if v == c else v)
print(json.dumps({'singleton_steps': {'graphs': graphs, 'graph_singleton_pairs': pairs,
    'steps': steps, 'mismatches': bad}}))


def rank2(M):
    rows, r = [row[:] for row in M], 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(r, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][j]:
                rows[i] = [a ^ b for a, b in zip(rows[i], rows[r])]
        r += 1
    return r


matrices = [[[int(edge(s, t) in E) for t in range(3, 6)] for s in range(3)] for E in (G, H)]
ranks = list(map(rank2, matrices))
print(json.dumps({'cut_ranks': {'matrices': matrices, 'GF2_ranks': ranks,
    'd_C': [3-r for r in ranks], 'C_size': 3, 'lemma15_required_d_C': 2}}))
PY
```

Output:

```json
{"witness": {"outside_degrees": [[1, 1, 1], [1, 2, 2], [1, 2, 2], [1, 2, 2], [1, 3, 1], [3, 1, 1], [1, 1, 1]], "connected": [true, true], "edge_counts": [5, 5], "internal_C_edges": [2, 0]}}
{"orbits": {"star_size": 5, "diamond_size": 11, "relabelled_diamond_hits": 0, "star_edge_counts": [3, 3, 3, 3, 6], "diamond_edge_counts": [3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5]}}
{"restricted_steps": {"graphs": 4096, "inside_steps": 12288, "inside_mismatches": 0, "eligible_outside_steps": 6960, "outside_mismatches": 0}}
{"singleton_steps": {"graphs": 1099, "graph_singleton_pairs": 5405, "steps": 26705, "mismatches": 0}}
{"cut_ranks": {"matrices": [[[0, 0, 1], [0, 1, 0], [1, 0, 0]], [[0, 0, 1], [0, 1, 0], [1, 0, 0]]], "GF2_ranks": [3, 3], "d_C": [0, 0], "C_size": 3, "lemma15_required_d_C": 2}}
```

## ASSUMED-UNVERIFIED

The formal conclusion concerns labelled LC-equivalence as defined above.
It does not assert minimality of six vertices or classify all condensation
sets that preserve equivalence. 逃逸审计未完成 (CLAUDE.md §3.9 exception): the obstruction and the missing evidence are recorded in https://github.com/the-omega-institute/trureturing/issues/11473#issuecomment-5922854877.
