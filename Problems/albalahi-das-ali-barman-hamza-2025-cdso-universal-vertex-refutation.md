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
| 4 | 2 | 1 | 1 | 6.221615262992 | $(3,3,2,2)$ | `C\|` |
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

### Mechanism and the range of the failure at $\ell=1$

- **Proved (by the settled comparison):** For $\ell=1$ a graph with a universal vertex is unique up to isomorphism. It is the hub of degree $n-1$ carrying one triangle and $n-3$ pendant vertices. Its CDSO is
  $U_n=2\sqrt{(n-1)^2+4}/(n-1)+\sqrt2+(n-3)\sqrt{(n-1)^2+1}/(n-1)$.
- **Computed:** The graph $T_n$ is obtained by moving one hub pendant onto a triangle vertex. Its hub has degree $n-2$, with neighbours of degrees $3$ and $2$, and the moved pendant hangs from the degree-3 vertex. Its CDSO is
  $T_n=\sqrt{(n-2)^2+9}/(n-2)+\sqrt{(n-2)^2+4}/(n-2)+\sqrt{13}/3+(n-4)\sqrt{(n-2)^2+1}/(n-2)+\sqrt{10}/3$.
  The sign of $T_n-U_n$:
  - positive for $n=5,6$: $0.214265$ and $0.057839$;
  - negative for every $7\le n\le 20000$, with the smallest gap $U_n-T_n=0.018996$ at $n=7$;
  - tending to $\sqrt{13}/3+\sqrt{10}/3-1-\sqrt2\approx-0.158271$.

  So the CDSO half of Conjecture 4.1 fails at $\ell=1$ for every computed order $7\le n\le 20000$. An all-$n$ proof is open.
- **Mechanism:** On a universal hub, each edge to a pendant costs about $1$. A triangle on the hub costs about $2+\sqrt2$ for its three edges. Moving one pendant onto a triangle vertex replaces the triangle edge $\sqrt2$ and a hub pendant edge by $\sqrt{13}/3+\sqrt{10}/3$. Once the hub degree is large enough for its edges to cost nearly $1$, this is cheaper by about $0.158$. At $\ell=0$ the star still minimizes, so the intuition from trees and from all connected graphs does not carry over to a fixed positive cyclomatic number.

Script for the computed items above, run with Python 3. Exit code: 0. Script SHA-256: `b30e70f6ef5da3ca6a25008b11e645bd003133992d179165ef9ffb6f839bc061`.

```python
from math import sqrt
f=lambda x,y: sqrt(x*x+y*y)/max(x,y)
def U(n):
    d=n-1
    return 2*f(d,2)+f(2,2)+(n-3)*f(d,1)
def T(n):
    d=n-2
    return f(d,3)+f(d,2)+f(3,2)+(n-4)*f(d,1)+f(3,1)
for n in (5,6,7,8,10,20,100,1000):
    print(n, f"{T(n)-U(n):.6f}")
print(all(T(n)<U(n) for n in range(7,20001)), f"{min(U(n)-T(n) for n in range(7,20001)):.6f}")
```

### What the refutation changes in the source

- **Checked (source read):** The arXiv v1 TeX states every result of the paper in Sections 2 and 3, before the concluding remarks. Section 2 has five propositions, two lemmas and one theorem quoted from Deng et al. Section 3 has six propositions and one corollary. None of them cites the conjectured statement. Conjecture 4.1 appears only in Section 4, "Concluding Remarks", as a question for further work. No proved result of the paper depends on it, so all of them stand.
- **Consequence:** Conjecture 4.1 is a conjunction. Its CDSO half is false, so the conjecture as stated is refuted. Its HSO half is a separate assertion about maximizers and remains open.
- **Consequence for the follow-up question:** Conjecture 4.2 concerns maximizers of CDSO and minimizers of HSO for $\ell\ge2$, the opposite extremal problems. It does not use the CDSO-minimizer statement, so this refutation leaves it open.
- **Revised CDSO statement:** Within the computed scope, a universal vertex in the CDSO minimizer holds at $\ell=1$ exactly for $3\le n\le 6$, and at $\ell\in\{2,3\}$ for every computed order $n\le7$. Whether $\ell\ge2$ also fails for larger $n$ is open.

- **Open:** The HSO half of Conjecture 4.1 is not addressed.
- **Open:** Conjecture 4.2, concerning minimum and maximum degrees in $\{2,3\}$ for $\ell\ge 2$ and $n>5(\ell-1)$, is not addressed.
- **Open:** Whether the CDSO half holds for every $\ell\ge 2$ remains open beyond the computed atlas scope.

## ASSUMED-UNVERIFIED

The atlas computation is numerical and is not a kernel proof. The atlas completeness and the absence of an external later settlement are treated as literature and computation inputs recorded by issue #13438. The HSO half and Conjecture 4.2 remain open.
