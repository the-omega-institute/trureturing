# Universal refutation of the linear domination conjecture for graph covers

The original assertion and graph conventions are recorded in
Library/notes/annor2025domination.md. The source conjectures a positive
universal lower-bound constant. The mathematical assertion below is the
repository's proposed refutation, not a theorem attributed to the source.

For a finite simple graph H, gamma(H) is the minimum cardinality of a
dominating set, where every vertex either belongs to the set or has a
neighbor in it. A k-fold cover consists of finite simple graphs G,F and
an onto map p:V(G)->V(F) which restricts to a bijection on each open
neighborhood and whose every fiber has cardinality k.

Proof: for any finite d-regular F of order N, label each fiber by a star
and d ports, one for each neighbor. Across an edge with endpoint port
labels a,b, send the star to b, a to the star, and b to a when b differs
from a; fix the other labels. Reverse transport is inverse transport.
This gives a (d+1)-fold simple cover dominated by its N stars. No matching
existence hypothesis is assumed.

Put t=r+1 and take the direct product of t complete graphs on 2*t+1
vertices. Its order is N=(2*t+1)^t and its degree is d=(2*t)^t. To defeat
any set of fewer than t vertices, agree with each selected vertex in its
own coordinate and use a spare coordinate to differ from all selected
vertices. This constructs an undominated vertex, so gamma(F)>=t. A value
different from two given values exists in each coordinate, giving a
common neighbor and hence connectedness. Bernoulli's inequality gives
d/N >= 1-t/(2*t+1) >= 1/2. Consequently gamma(G)<=N<=2*d,
and the positive fold k=d+1 satisfies gamma(G)/(k*gamma(F))<=2/t.
For any c>0 choose r>2/c; the inequality is then strict.

The product-graph domination ingredient is known (see
Library/notes/vemuri2019domination.md). Perfect-code constructions are
also an established subject; no new-ingredient or separate solved-problem
credit is claimed. Novelty of the universal refutation remains subject
to independent review and the limits of the bounded later-literature check.

Lean uses Mathlib SimpleGraph, finite function types, equivalences,
neighborhood cardinalities, and Bernoulli's inequality. Its domination
definitions and two minimum lemmas are a scoped Apache-2.0 source port
from formal-conjectures commit 8323e878b83fcd7f4a448256069352a265460d75;
copyright, full license and the pin-relative retirement condition are
preserved with the code. No new axiom or unproved mathematical input is used.

## 1. Universal counterexample family

For every positive real c there exist finite vertex types V and W,
simple graphs F on V and G on W, a function p:W->V and a natural k>0
such that F is connected, p is an onto local open-neighborhood bijection,
every fiber of p has cardinality k, and gamma(G)<c*k*gamma(F).

## 2. Negation of Conjecture 14

There is no positive real c such that, for every two finite vertex types
V,W, every pair of simple graphs F on V and G on W, every function
p:W->V and every natural k>0, if p is an onto local open-neighborhood
bijection and every fiber has cardinality k, then
c*k*gamma(F)<=gamma(G).

## 3. Regular-cover ingredient

For every finite vertex type V, every simple graph F on V with decidable
adjacency, and every natural d such that F is d-regular, there exists a
simple graph G on V times Option(Fin d) for which the first projection is
onto, induces a bijection on every open neighborhood, has every fiber of
cardinality d+1, and satisfies gamma(G)<=card(V).

## 4. Product-domination ingredient

For all naturals r,m with r<=m, let H be the categorical product of r+1
complete graphs on m+1 vertices: its vertices are functions Fin(r+1) to
Fin(m+1), and adjacency means inequality in every coordinate. Then
r+1<=gamma(H).
