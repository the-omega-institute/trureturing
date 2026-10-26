---
slug: zhang-2026-threshold-hypergraph-independence-polynomial
bibkey: zhang2023thresholdindependence
doi: 10.1016/j.dam.2025.07.017
url: https://arxiv.org/abs/2303.01024v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.result
---

# Independence polynomials do not determine T2-threshold hypergraphs

## Problem

E. Zhang, *On the Independence Polynomial and Threshold of an Antiregular
k-Hypergraph*, arXiv:2303.01024v1, Section 5, asks:

> Alternatively, a more general question is, given two T2-threshold
> k-hypergraphs with the same independence polynomial, are they isomorphic?
> These are left for future work.

The universal positive answer is false. The settling declaration is
`D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.result`.
The preregistration is [#19406](https://github.com/the-omega-institute/trureturing/issues/19406).
The formal result uses five vertices and $k=3$; no arbitrary-$N$ theorem is delivered.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| A finite $k$-uniform hypergraph | `KHypergraph k V`, its `edges` and `uniform` fields | Every edge has cardinality $k$. |
| No hyperedge is contained in an independent subset | `IsIndependent` | Every edge and subset are tested. |
| Equation (8), the sum of $x^{|S|}$ over independent subsets | `indepPoly` | Integer coefficients; includes the empty set. |
| Definition 4.1(T2), real labels and a strict threshold on every $k$-subset | `IsT2Threshold` | Literal strict inequality, with no positivity restriction on labels. |
| Isomorphism | `Isomorphic` | A vertex equivalence preserves membership of every edge. |
| Any two such hypergraphs with equal polynomials are isomorphic | `claim` | Quantifies over $k$, both finite vertex types and both hypergraphs. |
| Negative answer | `result` | Negates the complete universal implication using $k=3$ and `Fin 5`. |

The encoding permits $k=0,1,2$, whereas the source question concerns $k\ge3$;
the counterexample lies within the source range and all its edges are nonempty.
The finite-type instances enumerate vertices and decide equality; they add no
mathematical restriction to the finite source objects. The carrier `Polynomial ℤ`
is the formal integer-coefficient expression of Equation (8).

## Motivation

An independence polynomial records the number of independent subsets of each
size. The pair here has equal size profiles but different vertex-incidence
counts. Thus the polynomial loses information needed for isomorphism even
inside the T2-threshold class.

## Gap

Example 3 in the source gives non-isomorphic hypergraphs with equal independence
polynomials, but establishes T2 only for one of them. The present pair satisfies
T2 on both sides. The narrower antiregular identification is not established.

## Route

Index the vertices by $0,1,2,3,4$. Let $H$ contain every triple except
$012,013,014$, and let $K$ contain every triple except $012,013,023$.
The labelings are $(0,0,1,1,1)$ with threshold $1$ for $H$, and
$(0,1,1,1,3)$ with threshold $2$ for $K$. The private helpers
`h5_threshold` and `k5_threshold` check these certificates.

The private helper `polynomials_equal` enumerates the independent subsets and
proves equality of the two polynomials. The private helper `degree_transport`
uses `Finset.card_bij` to transport incident-edge counts across a vertex
bijection. The private helper `not_isomorphic` uses degree $5$ at vertex $2$
of $H$ and absence of degree $5$ in $K$. All five helpers occur on the live
proof path of `result` and are classified `bind-only`.

## Falsifier

An isomorphism of the displayed pair would preserve the number of edges
incident to each vertex. It would send vertex $2$ of $H$ to a vertex of $K$
of degree $5$, contradicting the checked degree obstruction. A source-reading
change that excludes this pair from T2 would invalidate the correspondence;
Definition 4.1(T2) is represented with its real labels and strict inequality.

## Evidence

The kernel-checked `result` refutes the universal claim, using the private
threshold, polynomial and non-isomorphism certificates. Its axiom closure is
contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
No atom or coverage edge is used; the admission basis is
`open-problem-resolution (#19406; Refuted)`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There are no other public theorems or published owner declarations in this delivery.

### Experiment

The independent finite computation is
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/a2c892b2d83ecae613ebfdbe7d4b628faddb2f58/docs/reports/zhang-2023-threshold-hypergraph-independence).
Its script is `check.py`, SHA-256
`72434578a87af92ee58b5f03c081f20e7e2e83a3527fb6a275ae6b4d842e4824`.
Command: `git -C ../trureturing-experiments show a2c892b2d83ecae613ebfdbe7d4b628faddb2f58:docs/reports/zhang-2023-threshold-hypergraph-independence/check.py | python3` (exit $0$).
For exactly $N=5,6,7,8$, it checks both T2 labelings on every triple,
the coefficient lists $(1,N,\binom N2,3,0,\ldots,0)$, and non-isomorphism
by all $N!$ vertex permutations. The coefficient lists are respectively
$(1,5,10,3,0,0)$, $(1,6,15,3,0,0,0)$,
$(1,7,21,3,0,0,0,0)$ and $(1,8,28,3,0,0,0,0,0)$.
The program reports `RESULT PASS`; its tested scope is finite.

## Triage

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| The universal T2-threshold isomorphism assertion fails at $k=3$ on five vertices, with all hypotheses discharged. | Proved in Lean: `result`, using `h5_threshold`, `k5_threshold`, `polynomials_equal` and `not_isomorphic`. | A single counterexample settles the universal question. |
| Equal independent-set size profiles coexist with a degree-$5$ obstruction to isomorphism. | Polynomial equality and the degree obstruction are kernel-checked in the private helpers `polynomials_equal` and `not_isomorphic` used by `result`; the explicit coefficient profile is computed by the pinned experiment at $N=5$. | This evidence concerns the displayed pair. |
| The supplied checker passes $N=5,6,7,8$. | Computed only: the pinned experiment, command, exit code and SHA-256 above. | No arbitrary-$N$ Lean theorem is delivered. |
| Identification with an antiregular hypergraph. | ASSUMED-UNVERIFIED: #19406 names $H_5$ while the supplied search answer identifies $K_5$. | An exact-definition check is required; neither identification is used. |
| T1 uniqueness, other restrictions and larger non-edge patterns. | Open / outside scope. | No conclusion about these restrictions follows from this delivery. |

### What the settlement shows

The mechanism for this pair is that the independent-set size profile retains
three independent triples but loses their intersection pattern. Polynomial
equality and the non-isomorphism obstruction are checked on the same five-vertex
objects; the explicit profiles are computed by the experiment. The degree-$5$
obstruction supplies the structural distinction.

The nearest surviving statements are the source's independently proved
polynomial formulas and threshold results: they do not require a positive
answer to its closing question. No stronger uniqueness theorem, T1 analogue,
arbitrary-size formal family or antiregular identification is established here.
The source's separate antiregular uniqueness question remains open within this
delivery. No other theorem of the source is asserted to be refuted.

### Literature status

The source and literature readings attributed to the orchestrator in #19406
cover Equation (8), Definition 4.1(T2), Example 3 and Section 5 of arXiv v1.
The search seat screened the author's works 2306.15180, 2502.02097 and
2609.12293 and the related paper 2602.21382; it reported no settlement and zero
citations in OpenAlex and Crossref. MathDB was not located. These are the
recorded search bounds, not a proof of absence of prior work.

## ASSUMED-UNVERIFIED

The final subscription journal text has not been read. The literature screen's
completeness, worldwide priority and the antiregular identification remain
ASSUMED-UNVERIFIED. The computed $N=5,6,7,8$ checks do not establish an
arbitrary-$N$ formal family. The journal DOI locates the source; the quoted
statements are from arXiv:2303.01024v1.
