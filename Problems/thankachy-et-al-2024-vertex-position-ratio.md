---
slug: thankachy-et-al-2024-vertex-position-ratio
bibkey: thankachyetal2024vertexposition
doi: 10.7151/dmgt.2491
url: https://arxiv.org/abs/2209.00359v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.result
---

# The vertex position ratio is unbounded on connected graphs

## Problem

Problem 2.4 of M. Thankachy, E. J. Thomas, U. Chandran, J. Tuite,
G. Di Stefano and G. Erskine, “On the Vertex Position Number of Graphs”,
asks: “Is the ratio $\mathrm{vp}(G)/\mathrm{vp}^-(G)$ bounded for connected
graphs?” The source is arXiv:2209.00359v2, page 5, published in Discussiones
Mathematicae Graph Theory 44 (2024), 1169–1188, DOI `10.7151/dmgt.2491`.

For a fixed vertex $x$, an $x$-position set excludes every other selected
vertex from every shortest path from $x$ to a selected vertex. The maximum
size is $p_x(G)$; its maximum and minimum over vertices are
$\mathrm{vp}(G)$ and $\mathrm{vp}^-(G)$. Endpoints belong to geodesics,
so $\{x\}$ is permitted but a set containing $x$ and another vertex is not.
The Lean definitions use the full finite carrier and all its subsets.

## Motivation

The source's Lemma 2.3 constructs ratios approaching six. The authors'
survey “General position problems in graphs”, arXiv:2501.19385v5, lists
Problem 2.4 as open. Issue [#15320](https://github.com/the-omega-institute/trureturing/issues/15320)
records the source, literature scope and exact finite-simple-graph conventions.
The settling declaration is
`D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.result`.

## Gap

Connectedness alone does not control the disparity between the position
numbers seen from two vertices. The ratio question asks for one real bound
uniform over all finite nonempty connected simple graphs; the Lean `claim`
states this by multiplication by the positive minimum position number.
No fixed order, degree bound or graph-class restriction is imposed.

## Route

For each $m\ge2$, let $N=4m$, $a_j=2m+2j$ and $b_j=2m+j+1$ for
$1\le j\le m$. The graph $G_m$ consists of a common hub $y$, a path $H$
of length $N$, $m$ paths $P_i$ of length $N$, and $m$ paths $Q_j$ of length
$a_j$. Their index-zero vertices are identified with $y$. Add edges from
$H_{b_j}$ to $Q_{j,b_j}$ and from $Q_{j,a_j}$ to every $P_{i,a_j}$.

The level function changes by at most one on each edge. Explicit ray walks
therefore realize the distance from $y$. A $y$-position set contains at most
one vertex from each ray, or is the singleton $\{y\}$, giving
$p_y(G_m)\le2m+1$. Put $x=H_N$. A second edge potential and explicit walks
place the $m(m-1)$ distinct vertices $P_{i,a_j+1}$, $1\le j<m$, on the sphere
of radius $2m+1$ around $x$. A sphere is an $x$-position set. Hence
$\mathrm{vp}(G_m)\ge m(m-1)$ and $\mathrm{vp}^-(G_m)\le2m+1$.
For every proposed real bound $C$, some $m\ge2$ satisfies
$m(m-1)>\max(C,0)(2m+1)$, contradicting `claim`.

## Falsifier

A uniform bound compatible with this family, a failure of connectedness,
or a failure of one of the two position-number inequalities would defeat
the route. The kernel-checked `result : ¬ claim` rules out the uniform bound
under the binding definitions. The finite computations below are independent
checks of the construction, not premises of the Lean proof.

## Evidence

`result` is frozen through `make deposit-uncovered`, without an atom or cover.
Its Scribe node carries the sole `OpenProblemResolutionClaim`, `Refuted`.
The axiom closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The mathematical source note is
`Library/GraphInvariants/thankachyetal2024vertexposition.md`.

The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9). There are no other
new public theorems; the family and bound helpers are private declarations
used in the settling proof.

### Experiment entry

[Vertex position ratio check](https://github.com/the-omega-institute/trureturing-experiments/tree/b5c971feb8074e350659821de9637747170944f3/docs/reports/thankachy-et-al-2024-vertex-position-ratio)
in `the-omega-institute/trureturing-experiments`, commit
`b5c971feb8074e350659821de9637747170944f3`, script
`docs/reports/thankachy-et-al-2024-vertex-position-ratio/check.py`.
Run `python3 check.py` from that directory. Exit code: 0; final reading:
`bad= 0`. Script SHA-256:
`2a442018e72257213bdefea8fb6aa729b1163126fcac1fab61e07f1bc422fda5`.

Exact BFS checks vertex and edge counts, connectivity, the $2m+1$ geodesic
rays from $y$, and the $m(m-1)$ selected vertices at distance $2m+1$ from $x$
for every $m=2,\dots,14$. Brute force checks the two position sets only for
$m=2,3$: the selected sphere vertices for $x$ and the neighbours of $y$ for
$y$. At $m=14$, the order is $1443$ and the certified ratio lower bound is
$182/29=6.275862\dots>6.27$. The computation does not claim exact values of
$\mathrm{vp}$ or $\mathrm{vp}^-$, nor a brute-force position check for $m>3$.

## Triage

### What the settlement shows

- **Kernel-checked, every $m\ge2$:** The edge-level bound (`level_edge`),
  shortest hub rays (`root_dist`, `same_ray_onGeodesic`) and ray counting
  (`hub_upper`) give $p_y(G_m)\le2m+1$. These are private helpers of `result`.
- **Kernel-checked, every $m\ge2$:** The second potential and explicit walks
  (`selected_distance_lower`, `selected_distance_upper`, `selected_distance`)
  put $m(m-1)$ distinct vertices (`selected_injective`) at distance $2m+1$
  from $x=H_N$. `sphere_position` and `x_lower` give $p_x(G_m)\ge m(m-1)$.
- **Kernel-checked, every $m\ge2$:** `family_bounds` gives
  $\mathrm{vp}(G_m)\ge m(m-1)$ and $\mathrm{vp}^-(G_m)\le2m+1$;
  `ratio_growth` and `result` refute a uniform bound. These are bounds,
  not kernel-checked exact invariant values.
- **Proved in prose:** Every singleton is a position set, so each $p_v(G)$
  is at least one and their nonempty minimum is positive. Dividing the
  kernel-checked family inequalities by this positive minimum gives
  $\mathrm{vp}(G_m)/\mathrm{vp}^-(G_m)\ge m(m-1)/(2m+1)$.
  This quotient statement is a consequence of the inequalities, not a
  separately named Lean declaration.
- **Computed:** The experiment entry checks the counts, geodesic rays and
  sphere by exact BFS for $m=2,\dots,14$, and the two position sets by brute
  force for $m=2,3$. At $m=14$, $n=1443$ and the ratio is at least
  $182/29>6.27$, exceeding six. Its command, exit code and script hash are
  given in the single experiment entry above.
- **Proved in prose:** The order is
  $n=1+(m+1)4m+\sum_{j=1}^m(2m+2j)=7m^2+5m+1$.
  The common hub is counted once, with each positive-index ray vertex
  counted separately. Thus $n/m^2\to7$ and
  $[m(m-1)/(2m+1)]/m\to1/2$, so the family lower bound has order
  $\sqrt n$. This order calculation is not a declaration of the module.
- **Open:** The growth rate of the maximum ratio over all connected graphs
  on $n$ vertices, including a matching upper bound and interpolation beyond
  the orders attained by this family.
- **Open:** The ratio question for trees and for graphs of bounded degree,
  and the analogous ratios for the other position-type invariants in the
  survey. This family imposes neither of those restrictions.
- **Kernel-checked surviving statements:** Equal-distance spheres remain
  position sets (`sphere_position`), and the separate hub upper bound and
  far-vertex lower bound hold uniformly on this family. No universal bound
  on connected graphs survives the settlement.
- **Literature reading:** Lemma 2.3's ratios approaching six remain examples.
  The source's separate degree, eccentricity and graph-class results retain
  their stated hypotheses; `result` refutes Problem 2.4, not those separate
  statements. Restricted-class and other-invariant questions remain open
  here and require their own source and literature checks.

## ASSUMED-UNVERIFIED

The literature screen is the scope recorded in #15320; no exhaustive claim
about all publications is made. Exact $\mathrm{vp}(G_m)$ and
$\mathrm{vp}^-(G_m)$ for the full family are not established by `result` or
by the experiment. The finite computation stops at $m=14$ for BFS and $m=3$
for brute force; extensions of those computational readings are unverified.
