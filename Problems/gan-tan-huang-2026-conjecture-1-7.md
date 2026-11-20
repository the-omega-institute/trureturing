---
slug: gan-tan-huang-2026-conjecture-1-7
bibkey: gantanhuang2026extremalcycles
doi: 10.48550/arXiv.2611.22824
url: https://arxiv.org/abs/2611.22824v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.result
---

# Gan–Tan–Huang Conjecture 1.7 on long paths

## Problem

Let $G$ be a finite simple connected undirected graph with $n$ vertices and
let $k,d$ be positive integers with $k\le d<n$. Write
$q=\lfloor(k-3)/4\rfloor$ and let $\theta_+^G$ count the vertices of degree
at least $d$. Conjecture 1.7 asserts that $G$ contains a simple path on
$k+1$ vertices whenever
$$
\theta_+^G\ge
\frac{q(n-1)}d+\left(1-\frac qd\right)\frac{(n-1)q}{q+d(d-1)}+2.
$$
The source fixes the degree count and path order in Definitions 2.1 and 2.2.
[Conjecture 1.7](https://arxiv.org/html/2611.22824v1#S1.Thmlemma2026ErdosQuestion7)
· [Definitions](https://arxiv.org/html/2611.22824v1#S2)

## Motivation

The conjecture proposes a larger degree-count threshold in response to the
glued star constructions for the earlier Erdős–Faudree–Schelp–Simonovits
question about connected graphs. Private leaves test whether many neighbors
at each high-degree vertex can force additional interior vertices on a path.
[Question 1.6](https://arxiv.org/html/2611.22824v1#S1.Thmlemma2026ErdosQuestion6)
· [Li–Ma–Ning, §5](https://arxiv.org/abs/2102.04367v3)

## Gap

The threshold permits six high-degree vertices at $(n,d,k)=(24,8,8)$.
A nine-vertex path requires seven distinct interior vertices. High-degree
vertices in a clique can acquire all their remaining neighbors as private
leaves, each of which can only be a path endpoint.

The Tier 1 preregistration gives the full claim, a falsifiable finite test
and a bounded literature screen. The exact arXiv identifier and authors
had no matching result in the pinned repository base. The preregistration
records zero OpenAlex forward citations and no settlement of this claim
among eight Crossref matches. Li–Ma–Ning Proposition 5.2 constructs graphs
on its parameter progression with exactly one fewer high-degree vertex
than the revised threshold. It gives a lower bound on the connected
forcing number there. Gan–Tan–Huang Theorem 1.8 gives a different threshold
for cycles.
[Preregistration #31996](https://github.com/the-omega-institute/trureturing/issues/31996)
· [Prospective forecasts](https://github.com/the-omega-institute/trureturing/issues/31996#issuecomment-7027229718)

## Route

Form a clique on six core vertices and attach three private leaves to
each core vertex. This graph is connected and has 24 vertices and 33 edges.
Its six core vertices have degree eight, and its 18 leaves have degree one.
For $d=k=8$, the integer floor is $q=1$, the second denominator is 57,
and the exact threshold is $298/57=6-44/57$.

A leaf has one neighbor. Every interior position of an injective path
has distinct predecessor and successor, so the seven interior positions
of a nine-vertex path must all be in the core. The resulting injection
$\mathrm{Fin}(7)\to\mathrm{Fin}(6)$ contradicts finite cardinality.

## Falsifier

The finite witness would fail if it violated connectedness or the exact
degree threshold, or if an injective nine-vertex path existed. A mismatch
in the source quantifiers, signed floor, threshold or path order would
invalidate the claim correspondence.

## Evidence

The frozen Lean theorem
`D5/S3/Combinatorics/Graph/Walks/GanTanHuangConjecture17Refutation.result`
has type `Not claim`. The source claim uses integer division by positive
four for the floor and exact rational threshold arithmetic. Its
denominators are nonzero throughout $0<k\le d<n$. The first is positive.
For the second, $q\ge-1$. At $d=1$ it is $-1$, and for $d\ge2$ it is at
least one.

## Triage

- **Proved in Lean.** The finite witness refutes Conjecture 1.7.
- **Computed.** The longest path in the witness has eight vertices.
  The interior-position argument gives the upper bound. A path from
  a leaf across all six cores to a leaf at the last core attains it.
- **Computed.** For Question 1.6 the earlier threshold
  $q\lfloor(n-1)/d\rfloor+2$ is four at $(24,8,8)$. The same graph
  exceeds both thresholds and also gives a finite counterexample to
  that already-refuted question. Li–Ma–Ning Proposition 5.2 gives the
  historical counterexamples for $k\ge7$ on other parameter progressions.
  [Question 1.6](https://arxiv.org/html/2611.22824v1#S1.Thmlemma2026ErdosQuestion6)
  · [Li–Ma–Ning, Proposition 5.2](https://arxiv.org/abs/2102.04367v3)
- **Proved on paper.** For each integer $t\ge2$, take $d=k=4t$ and a
  clique on $m=4t-2$ vertices with three private leaves per core. Then
  $n=16t-8$, there are $m$ vertices of degree $d$, and paths have at most
  $m+2=k$ vertices. With $q=t-1$ and $D=q+d(d-1)=16t^2-3t-1$, the threshold
  simplifies to $2+(n-1)qd/D$. The slack is
  $m-2-(n-1)qd/D=4(t-1)(6t-1)/D>0$. This family varies $n$, $d$ and $k$
  together. The Lean settlement uses $t=2$.
- **Proved by the witness and a published bound.** Write $\psi(n,d,k)$
  for the least integer degree count that forces a path on $k+1$
  vertices among connected graphs. The witness gives $\psi(24,8,8)\ge7$.
  The unrestricted forcing number $\varphi(24,8,8)$ is seven by
  Li–Ma–Ning Theorem 1.3(ii)(c), using $24=2(8+1)+6$ and $6=8-2$.
  Connected graphs form a subclass, so $\psi(24,8,8)=7$.
  [Li–Ma–Ning, Definition 1.1, Theorem 1.3 and §5](https://arxiv.org/abs/2102.04367v3)
- **Open here.** The exact connected forcing number $\psi(n,d,k)$ in
  general and a sharp replacement for the conjectured threshold remain
  unresolved by this settlement. A minimum degree of two would exclude
  this leaf construction, and sufficiency under that additional
  hypothesis remains open here. The paper states its cycle theorem
  independently of Conjecture 1.7.
  [Gan–Tan–Huang, Theorem 1.8](https://arxiv.org/html/2611.22824v1#S1)

## ASSUMED-UNVERIFIED

The bounded literature screen leaves worldwide priority unverified.
The historical 1989 paper and Gan–Yi–Jiang's submitted cycle work are
identified through the pinned sources.
