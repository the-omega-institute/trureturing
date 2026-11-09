---
slug: das-2026-nonabelian-sgb-problem49
bibkey: das2026sgb
doi: 10.48550/arXiv.2601.04004
url: https://arxiv.org/abs/2601.04004v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SubgroupGenerating/EnergyBounds.result
---

# The full nonabelian subgroup-generating question

## Source and exact scope

Das–Erfanian–Nath, *Various spectra and energies of subgroup generating bipartite graph*,
arXiv:2601.04004v1, Problem 4.9, asks:

> Is there any finite non-abelian group G such that B(G) does not hold the conclusions of Remark 4.1?

The fixed source archive `Various_spectra_and_energies_of_SGB-graph.tex` defines the graph
at lines 98–118 and its matrices at lines 134–145; Remark 4.1 and Problem 4.9 are at
lines 1141–1155. The explicit $Q=D+A$ conflicts with nearby prose saying $D$. The formal
statement uses the explicit matrix, without asserting an author correction.

The prospective unit is [#28317](https://github.com/the-omega-institute/trureturing/issues/28317).
It concerns this entire question. The earlier #21358 and the cyclic extension in
arXiv:2602.07587v1 are separate records and retain their original scope.

For every finite nonabelian group $G$, the vertex carrier is
$(G\times G)\sqcup\operatorname{Subgroup}(G)$. All ordered and repeated pairs and all
subgroups remain present. A pair $(a,b)$ is adjacent precisely to $\langle a,b\rangle$;
there are no same-part edges. Put $M=|G|^2$, $k=|\operatorname{Subgroup}(G)|$, $n=M+k$.
There are exactly $M$ unordered edges. Let $A$ be adjacency, $D$ the degree diagonal,
$L=D-A$, $Q=D+A$, and $CN$ the zero-diagonal common-neighbor count matrix.
Spectra are real eigenvalue multisets with algebraic multiplicity. Integral means each
eigenvalue is the real image of an integer. The energies are

$$
E=\sum |\lambda(A)|,\qquad LE=\sum|\lambda(L)-d|,\qquad
LE^+=\sum|\lambda(Q)-d|,\qquad E_{CN}=\sum|\lambda(CN)|,
\quad d=\frac{2M}{n}.
$$

The full conjunction is adjacency nonintegrality; integrality of $L,Q,CN$;
$E<n$; $E\le2(n-1)$; $LE\le2(n-1)$; $LE^+\le2(n-1)$;
$E_{CN}\le2(n-1)(n-2)$; and $E\le LE$.
The Lean result states these scalar inequalities directly. It does not use the existing
`sourceBundle` predicate or assume a formula for its actual complete-graph energies.

## Mathematical route

Write $r_H$ for the cardinality of all ordered generating pairs of $H$, and $t$ for the
number of positive fibers. Every subgroup center has its complete star $K_{1,r_H}$;
a zero fiber is an isolated center. The formal proof identifies entries of the actual
four source matrices, constructs each full fiber equivalence, factors the characteristic
polynomial into all subgroup blocks, and identifies the characteristic roots with the
actual Hermitian spectra. No multiplicity, fiber cardinality or characteristic polynomial
is supplied as an unproved premise.

For $r\ge1$, a star has spectra

$$
A:\{\sqrt r,-\sqrt r,0^{(r-1)}\},\quad
L,Q:\{0,r+1,1^{(r-1)}\},\quad
CN:\{0,r-1,(-1)^{(r-1)}\}.
$$

For $r=0$ every spectrum is the singleton zero. Thus

$$
E=2\sum_H\sqrt{r_H},\quad E_{CN}=2(M-t),\quad
LE=LE^+=kd+(M-t)|1-d|+M+t-td.
$$

The fiber partition gives $\sum r_H=M$; the degree-sum identity gives the actual edge
count and the single center $d$. Cauchy's theorem supplies an actual prime-order subgroup
of order $p$, with $r_H=p^2-1$. Every pair in that subgroup other than $(1,1)$ generates
it. Since $p-1<\sqrt{p^2-1}<p$, adjacency is nonintegral and
$2\sqrt{r_H}<r_H+1$. Summing $2\sqrt r\le r+1$ gives $E<n$.

The identity fiber has size one, and every other positive fiber has size at least three.
A noncommuting pair $a,b$ supplies six distinct generating pairs for the same subgroup:
$(a,b),(b,a),(a,ab),(ab,a),(b,ab),(ab,b)$. Therefore

$$
\sum_H\sqrt{r_H}\le M-t.
$$

Indeed $\sqrt r\le r-1$ for $r\ge3$, and $\sqrt r\le r-2$ for $r\ge6$;
the additional deficit compensates the identity fiber. If $d\le1$, then $M\le k$ and
$LE=2kd$, which is at least $2M$ and at most $M+k$. If $d\ge1$, then
$LE=2M-2t(d-1)$; $d<2$ and the deficit yield $E\le LE$, while $LE\le2M$.
Both branches give the stated upper bound. Finally $k,t\ge1$ give
$2(M-t)\le2(n-2)\le2(n-1)(n-2)$.

## Reuse, attribution and boundaries

The existing `CyclicExtensionRefutation` owns the literal carrier, graph, matrix choices,
Hermitian theorem, spectra, integrality predicate, global center and energies. Its cyclic
order-one refutation is a different result. The known star formulas are suppliers rather
than a claim of original literature novelty. Pinned Mathlib supplies Schur complements,
block-triangular characteristic polynomials, characteristic-root/eigenvalue equality,
Cauchy's theorem and the prime-cardinality subgroup dichotomy. No general bipartite
$E\le LE$ theorem is assumed.

The bounded source qualification found that arXiv:2602.07587v1 treats cyclic families
rather than the entire nonabelian question. The 2009 general-graph energy examples do not
realize this subgroup-generating graph. The 2010 Ky Fan primary text was not acquired and
no unverified statement from it is used. Authenticated third-party Lean searches for
star-graph and arrowhead characteristic polynomials returned no hits in those queried
scopes. Some primary literature remains unread; worldwide prior-resolution absence,
publication priority and private author intent are not established.

The mathematical source is `EnergyBounds.result`, with the three upstream content modules
and matching Blueprint Scribes. Its admission basis is the prospectively registered
external open-problem resolution. Every auxiliary declaration lies on the result's live
proof path. The proof-shape assessment and Reg source binding require independent review;
a compiled Reg proof alone does not establish `declared_validated`. This dossier records
the mathematical statement and its boundaries, without a terminal research settlement.
