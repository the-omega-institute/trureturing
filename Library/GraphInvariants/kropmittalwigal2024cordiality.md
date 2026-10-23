---
bibkey: kropmittalwigal2024cordiality
authors: Elliot Krop; Aryan Mittal; Michael C. Wigal
year: 2024
title: The Cordiality Game and the Game Cordiality Number
doi: 10.1007/s00373-024-02798-1
url: https://arxiv.org/abs/2403.18060v1
claim: "Section 1 defines the cordiality game and game cordiality number; Section 3 conjectures that every tree of order n has game cordiality number at most that of the path on n vertices."
strata_touched:
  - D5/S3/Combinatorics/Games/CordialityTreePathRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s00373-024-02798-1

Source: https://arxiv.org/abs/2403.18060v1

Journal: Graphs and Combinatorics 40, article 75.

## Game definition

Section 1, page 2 of the arXiv version:

> Let $G = (V,E)$ be a graph. The cordiality game is played on $G$ by two players, Admirable and Impish, who take turns selecting the unlabeled vertices of $G$. Admirable labels selected vertices by $0$ and Impish labels selected vertices by $1$. The labels on edges are then determined by the sum of incident vertex labels modulo $2$.

> In other words, after all the vertices are labeled, if we let $e_0$ be the number of edges labeled by $0$ and $e_1$ be the number of edges labeled by $1$, then we define the discrepancy to be $d = |e_1 - e_0|$. Then Admirable attempts to minimize $d$ and Impish attempts to maximize $d$.

> We define the game cordiality number, $c_g(G)$, to be the value of $d$ when both players play optimally. Further, to prove our claimed bounds, we create a variant of the cordiality game where Impish starts rather than Admirable.

Thus Admirable starts in $c_g$. An undirected edge is counted once. The zero-labelled
vertices form the set $A$; an edge has label one precisely when one endpoint belongs
to $A$ and the other does not.

## Tree–path conjecture

Section 3, Conjecture 3.2, page 9 of the arXiv version:

> For any tree $T$ of order $n$, $c_g(T)\le c_g(P_n)$.

The module `D5/S3/Combinatorics/Games/CordialityTreePathRefutation` refutes this
statement with the ten-vertex tree having edges $\{i,i+1\}$ for $0\le i\le6$,
$\{0,8\}$ and $\{0,9\}$. It proves that the tree has game cordiality number at
least three, whereas the path on ten vertices has game cordiality number at most one.
