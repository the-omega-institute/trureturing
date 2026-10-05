---
slug: albalahi-das-ali-barman-hamza-2025-cdso-universal-vertex-refutation
bibkey: albalahidasalibarmanhamza2025hyperbolicsombor
doi: 10.47443/dml.2025.176
url: https://www.dmlett.com/archive/v16/DML25_v16_pp108-115.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.result
---

# The order-seven unicyclic CDSO minimizer has no universal vertex

## Problem

Conjecture 4.1 states: “A graph minimizing (maximizing, respectively) the CDSO index (HSO index, respectively) among fixed-order connected graphs with cyclomatic number $\ell(\ge 1)$ has a vertex adjacent to all other vertices.” This dossier settles the CDSO half. The HSO half is outside the delivered claim.

## Motivation

The source presents the universal-vertex assertion after numerical tests on fixed-order connected graphs. The Lean module records the literal CDSO edge sum, the literal minimum edge-deletion definition of cyclomatic number, the fully quantified CDSO claim, and a kernel-checked refutation.

## Gap

The source did not settle whether every CDSO minimizer has a universal vertex. The open-problem registration in issue #13438 records the verbatim statement, the order-seven witness, the literature check, and the settlement criterion.

## Route

Let $T$ have vertex set $\{0,1,2,3,4,5,6\}$ and edges $01,02,12,03,04,05,16$. It is connected, has seven edges, and has cyclomatic number $1$. Its degrees are $(5,3,2,1,1,1,1)$ and

$$
{}^c\!\operatorname{DSO}(T)=\frac{\sqrt{10}}{3}+\frac{\sqrt{29}}{5}+\frac{\sqrt{34}}{5}+\frac{\sqrt{13}}{3}+\frac{3\sqrt{26}}{5}.
$$

A connected graph of order $7$ and cyclomatic number $1$ has seven edges. If it has a universal vertex, the remaining edge joins two of the other vertices, so its degree multiset is $(6,2,2,1,1,1,1)$ and its CDSO is

$$
\sqrt{2}+\frac{2\sqrt{10}}{3}+\frac{2\sqrt{37}}{3}.
$$

The Lean theorem proves the first value is strictly smaller by rational square-root bounds. A finite nonempty class has a minimizer; therefore every minimizer has value at most the value of $T$ and cannot have a universal vertex.

## Falsifier

A proof of the original CDSO assertion at $n=7$, $\ell=1$, or a universal vertex in a CDSO minimizer with the displayed comparison, would falsify this settlement. The delivered theorem `result : ¬ claim` rules out that possibility in the encoded finite-simple-graph model.

## Evidence

The declaration `D5.S3.Combinatorics.Graph.CdsoUniversalVertexRefutation.result` is frozen by `make deposit-uncovered` and has axiom closure contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$. The Scribe resolution claim is `Refuted`. The library source is the journal article cited in issue #13438, DOI `10.47443/dml.2025.176`, with its verified locator in the repository note.

## Triage

### What the settlement shows

- **Proved:** CDSO-UNIV fails at $n=7$, $\ell=1$. The witness $T$ has strictly smaller CDSO than every order-seven unicyclic graph with a universal vertex; the theorem proves that no minimizer has a universal vertex.
- **Computed:** In the atlas scan below, $T$ is the unique minimizer up to graph isomorphism for $(n,\ell)=(7,1)$. The computation is independent of the Lean theorem and does not supply its proof.
- **Computed:** The minimizer table for connected graphs with $n\le 7$ and $\ell\in\{1,2,3\}$ is reproduced by the inline script. The table records the number of connected atlas graphs, the number of tied minimizers, the numerical CDSO value, the degree multiset, and a graph6 representative.

| $n$ | $\ell$ | connected graphs | tied minimizers | minimum CDSO | degree multiset | graph6 representative |
|---:|---:|---:|---:|---:|---|---|
| 3 | 1 | 1 | 1 | 4.242640687119 | $(2,2,2)$ | `Bw` |
| 4 | 1 | 2 | 1 | 4.872006966072 | $(3,2,2,1)$ | `CN` |
| 4 | 2 | 1 | 1 | 6.221615262992 | $(3,3,2,2)$ | `C|` |
| 4 | 3 | 1 | 1 | 8.485281374239 | $(3,3,3,3)$ | `C~` |
| 5 | 1 | 5 | 1 | 5.711834352682 | $(4,2,2,1,1)$ | `D@{` |
| 5 | 2 | 5 | 1 | 6.920545234214 | $(4,3,2,2,1)$ | `DjW` |
| 5 | 3 | 4 | 1 | 8.122417494872 | $(4,4,2,2,2)$ | `DF{` |
| 6 | 1 | 13 | 1 | 6.627691193383 | $(5,2,2,1,1,1)$ | `E?Fw` |
| 6 | 2 | 19 | 1 | 7.763564957569 | $(5,3,2,2,1,1)$ | `EB{G` |
| 6 | 3 | 22 | 1 | 8.885629600736 | $(5,4,2,2,2,1)$ | `EzW_` |
| 7 | 1 | 33 | 1 | 7.558578027096 | $(5,3,2,1,1,1,1)$ | `FItA?` |
| 7 | 2 | 67 | 1 | 8.671301210987 | $(6,3,2,2,1,1,1)$ | `FmpA?` |
| 7 | 3 | 107 | 1 | 9.745817561672 | $(6,4,2,2,2,1,1)$ | graph6 `FzW` followed by a backtick and `?` |

Rows with no connected graph for $n<3$ or for $(n,\ell)=(3,2),(3,3)$ are omitted.

The computation was rerun with Python 3 using NetworkX's documented graph atlas. Exit code: 0. Script SHA-256: `e82216789083a7ef8e33a71caecbcfeda4166b466948e1cdc862e1cda35b4761`.

```python
import math
import networkx as nx
from collections import defaultdict

def cdso(G):
    d=dict(G.degree())
    return sum(math.sqrt(d[u]**2+d[v]**2)/max(d[u],d[v]) for u,v in G.edges())

def key(G):
    return tuple(sorted(dict(G.degree()).values(), reverse=True))
by=defaultdict(list)
for G in nx.graph_atlas_g():
    n=G.number_of_nodes()
    if 1 <= n <= 7 and n and nx.is_connected(G):
        ell=G.number_of_edges()-n+1
        if 1 <= ell <= 3:
            by[(n,ell)].append(G)
for n in range(1,8):
  for ell in range(1,4):
    gs=by.get((n,ell),[])
    if not gs:
      print(f"{n}\t{ell}\t(no connected graph)")
      continue
    vals=[cdso(g) for g in gs]
    m=min(vals); winners=[g for g,v in zip(gs,vals) if abs(v-m)<1e-12]
    g=winners[0]
    print(f"{n}\t{ell}\t{len(gs)}\t{len(winners)}\t{m:.12f}\t{key(g)}\t{nx.to_graph6_bytes(g,header=False).strip().decode()}")
```

- **Open:** The HSO half of Conjecture 4.1 is not addressed.
- **Open:** Conjecture 4.2, concerning minimum and maximum degrees in $\{2,3\}$ for $\ell\ge 2$ and $n>5(\ell-1)$, is not addressed.
- **Open:** Whether the CDSO half holds for every $\ell\ge 2$ remains open beyond the computed atlas scope.

## ASSUMED-UNVERIFIED

The atlas computation is numerical and is not a kernel proof. The atlas completeness and the absence of an external later settlement are treated as literature and computation inputs recorded by issue #13438. The HSO half and Conjecture 4.2 remain open.
