---
slug: gervacio-2026-vertex-identity-seidel-switches
bibkey: gervacio2026identityseidel
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.result
url: https://arxiv.org/abs/2601.04530v1
---

# Every vertex an identity Seidel switch

## Problem

S. V. Gervacio, *On identity Seidel switches*, arXiv:2601.04530v1,
Section 6, Problem 6.1, page 13:

> Characterize graphs $G$ for which every vertex is a vertex-ISS. Lemma 4.4 gives a necessary condition in terms of the minimum and maximum degree; can this be strengthened to a complete characterization?

The source's graphs are simple graphs on a nonempty finite vertex set.
Switching across $S$ complements exactly the pairs with one endpoint in
$S$. An identity Seidel switch (ISS) means $S(G)\cong G$; a vertex-ISS uses
$S=\{v\}$. The complete answer is $|V(G)|=1$.

## Motivation

The declaration
`D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.result`
proves the characterization for every finite nonempty simple graph, without
connectivity or regularity assumptions. The source definitions and locators
are in `Library/GraphInvariants/gervacio2026identityseidel.md`.

## Gap

Issue #14446 preregisters SEID-1 and the source definitions. Its literature
readings report only arXiv v1, no matching MathDB entry for the switch terms,
and no settlement in the searched scope. These are scoped literature
readings, not a proof of exhaustive priority. The author's
arXiv:2604.18984 concerns the pentagon graph operator.

## Route

Write $n=|V(G)|$ and $H=v(G)$. Partition the edges into incident and
nonincident edges. The latter are unchanged, and the new incident edges are
the complementary neighbour set. Thus
$|E(H)|+2\deg_G(v)=|E(G)|+(n-1)$.
An isomorphism preserves the edge count. If every vertex is a vertex-ISS,
then $2\deg_G(v)=n-1$ for every $v$, so all degrees are equal.
At order greater than one, this equation forces a positive degree; take a
neighbour $w$ of $v$. Switching at $v$ decreases the degree of $w$ by one,
contradicting degree preservation under an isomorphism to the regular graph.
At order one the adjacency relation is empty and the switch is the identity.

For an arbitrary cut $S$ and vertex $y$, let $C_y$ be the vertices on the
opposite side of the cut. The general degree balance is
$\deg_{S(G)}(y)+2|N_G(y)\cap C_y|=\deg_G(y)+|C_y|$.
The private `switch_degree_balance` proves this formula; it includes empty
and full cuts. Natural subtraction in the Lean singleton formulas is
truncated subtraction.

## Falsifier

A finite nonempty graph of order greater than one for which every singleton
switch is isomorphic to the graph would refute the characterization.
The all-vertices hypothesis is essential to the regularity step; one
vertex-ISS alone does not imply the conclusion. The source's same-vertex
wording in Lemma 4.4 is treated explicitly in Triage.

## Evidence

The canonical Lean source is
`D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.lean`.
It defines `seidelSwitch`, `IsVertexISS` and `claim`, and proves `result : claim`.
Its private degree and edge-count helpers lie on the proof path to `result`.
The graph-isomorphism invariants used in the proof are
`SimpleGraph.Iso.card_edgeFinset_eq` and `SimpleGraph.Iso.degree_eq`, imported
through `Mathlib.Combinatorics.SimpleGraph.Finite`.

The following independent exhaustive program enumerates all labelled simple
graphs on $\{0,\ldots,n-1\}$ for $1\le n\le6$, filters by the necessary
edge-count condition, and compares canonical edge lists over every vertex
permutation. Its source is the orchestrator's `/tmp/op-seidel/check.py`.
The implementation seat reran `python3 /tmp/op-seidel/check.py`, exit 0.
SHA-256:
`7b01b0b4d169e1af311039ef6139352d03d2171399b286c8593990218678719b`.
Copy the code into `check.py` and run `python3 check.py` to reproduce it.

```python
import itertools,sys
def canon(n,E):
    best=None
    for p in itertools.permutations(range(n)):
        f=tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in E))
        if best is None or f<best: best=f
    return best
res={}
for n in range(1,7):
    pairs=list(itertools.combinations(range(n),2)); cnt=0
    for mask in range(1<<len(pairs)):
        E=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
        Es=set(E)
        # quick necessary filter: switching v changes edge count by n-1-2deg(v)
        deg=[sum(1 for e in E if v in e) for v in range(n)]
        if any(n-1-2*d!=0 for d in deg): continue
        c=canon(n,E); ok=True
        for v in range(n):
            E2=[e for e in pairs if ((e in Es) != (v in e))]
            if canon(n,E2)!=c: ok=False;break
        if ok: cnt+=1
    res[n]=cnt
print(res)
```

Output: `{1: 1, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0}`.
The computation establishes only the tested finite scope; the Lean theorem
establishes the unbounded characterization.

## Triage

Tier 1; Problem 6.1 is **Proved** through SEID-1. The admission basis is
`open-problem-resolution` (#14446). All five theorem proofs are `bind-only`
after same-delivery expansion: the four helpers have live consumers, and
`result` is the external named settlement. Utility is `none`: the Lean
module contains general finite-graph arguments and no fixed numerical
certificate. There is no atom or coverage edge.

### What the settlement shows

- **Mechanism — proved in this module.** `vertex_edge_balance` and the
  isomorphism's edge-count equality force $2\deg_G(v)=n-1$. Applying this at
  every vertex forces regularity. `vertex_degree_off` gives degrees $d-1$
  for neighbours of the switched vertex and $d+1$ for its non-neighbours.
  For $n\ge3$ positive degree provides a neighbour, and this breaks
  regularity. For $n=2$, $2d=1$ is impossible. `result` combines these facts
  and proves the sharp order-one converse. The general cut-degree identity
  is proved by `switch_degree_balance`; no general cut-edge formula is claimed.
- **Lemma 4.4 — proved on paper for distinct vertices, with a literal
  wording boundary.** The source asserts that every minimum-degree vertex
  is adjacent to every maximum-degree vertex under the all-vertex-ISS
  hypothesis. The characterization leaves only one vertex, so the
  distinct-vertices version is vacuous. The literal unrestricted version
  permits the same vertex on both sides and is false: the sole vertex is
  both minimum- and maximum-degree but has no loop. Its proof's asserted
  degree increase requires distinct vertices. An order-at-least-two
  hypothesis is impossible by `result`, and also makes the implication
  vacuous. This paper argument is not an additional Lean declaration.
- **Natural weakening — open.** Characterize graphs in which every vertex
  lies in some nontrivial ISS of size at most two, allowing vertex-ISS or
  edge-ISS. The source's edge-ISS additionally requires that its two
  vertices are adjacent. This is a follow-up candidate; neither the theorem
  nor the exhaustive program tests it.
- **Problems 6.2–6.4 — unaffected, paper argument.** Their source clauses
  concern possible ISS-group orders, the interaction with automorphisms,
  and signed or weighted extensions. None assumes that every singleton is
  an ISS, and the theorem makes no conclusion about those domains. They
  remain open here. No other source result is used as a consequence of
  Problem 6.1; Lemma 4.4's boundary is the effect on the cited prerequisite.
- **Exhaustive check — computed.** For all labelled graphs with
  $1\le n\le6$, the counts are $1,0,0,0,0,0$. Evidence: the program in
  Evidence, command `python3 /tmp/op-seidel/check.py`, exit 0 and the
  SHA-256 above. The enumeration alone makes no claim for $n>6$.

## ASSUMED-UNVERIFIED

The issue's literature checks are orchestrator-reported; no exhaustive
novelty or priority claim is made. The natural weakening and Problems
6.2–6.4 are not settled. The paper analysis of Lemma 4.4 is not a separately
formalized theorem.
