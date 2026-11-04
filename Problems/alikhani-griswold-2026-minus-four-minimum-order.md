---
slug: alikhani-griswold-2026-minus-four-minimum-order
bibkey: alikhanigriswold2026integerdominationroots
doi: 10.48550/arXiv.2608.00109
url: https://arxiv.org/abs/2608.00109v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.result
---

# Refutation of order-33 minimality for domination root minus four

## Problem

Saeid Alikhani and Max Griswold, *On the Integer Domination Root Conjecture*,
arXiv:2608.00109v1, Section 4 item 2, printed page 5 asks:

> Is n=33 the minimal order of a graph admitting -4 as a domination root?

Section 1 uses finite nonempty connected simple undirected graphs. An
ordinary dominating subset S contains or neighbors every vertex, and each
subset is counted exactly once:

$$D(G,x)=\sum_{S\text{ dominates }G}x^{|S|}.$$

Connectedness applies to G; the dominating subsets need not induce connected
graphs. There is no degree, planarity, cyclomatic-number or
root-multiplicity restriction.

The complete positive claim includes both attainment at order 33 and
exclusion at every smaller positive order. Its exact Lean definition is:

~~~lean
def claim : Prop :=
  (∃ G : SimpleGraph (Fin 33),
      G.Connected ∧ ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card = 0) ∧
    (∀ n : ℕ, 1 ≤ n → n < 33 →
      ∀ G : SimpleGraph (Fin n), G.Connected →
        ∑ S ∈ domSets G, (-4 : ℤ) ^ S.card ≠ 0)
~~~

Here domSets is DominatingSetAverage.domSets. The designated result is
literally "theorem result : ¬ claim", with no parameters or extra hypotheses.
Its declaration GID is
D5/S3/Combinatorics/Graph/Domination/AlikhaniGriswoldMinOrderRefutation.result.

## Motivation

The source's Theorem 2.1 already supplies G33, a 33-vertex, 36-edge graph
whose domination polynomial has a factor x+4. That attainment is prior art.
A single connected graph of positive order below 33 with the same root
answers the minimum-order question negatively.

The unbounded connected-family question in Section 4 item 3 is separate.
Its repository result is
D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.result, associated
with unit [#25087](https://github.com/the-omega-institute/trureturing/issues/25087)
and [PR #25225](https://github.com/the-omega-institute/trureturing/pull/25225).
Neither G33 attainment nor that family result is a new conclusion of this
minimum-order refutation.

## Gap

The universal exclusion clause for 1 <= n < 33 is false: the counterexample
has 21 vertices and 25 edges. The argument does not exclude graphs of any
order below 21 and therefore does not determine the least possible order.
It also does not classify all connected graphs admitting this root.

## Route

The graph on Fin 21 is the symmetric closure of these undirected edges:

~~~text
(0,5), (0,6), (0,7), (0,13),
(1,3), (1,4), (1,5), (1,6),
(2,3), (2,4), (3,13), (4,13),
(5,6), (7,8), (7,9), (7,10), (7,11), (7,12),
(13,14), (13,15), (13,16), (16,17), (16,19),
(17,18), (19,20)
~~~

Its core is induced on vertices 0 through 6. The branches on 7 through 12
and 13 through 20 have roots 7 and 13 and core incidence sets {0} and
{0,3,4}. At integer weight -4, the omitted-root/selected-root message pairs
are (-1024,972) and (-3328,6912).

The existing general theorem
D5/S3/Combinatorics/Graph/Domination/MinusFourReassembly.zero_of_messages
is applied directly to this graph, its exact decomposition and that same
message table. The local graph laws, message equalities and covered-core
table cancellation are all proved. Explicit paths from vertex 0 establish
connectedness. Thus D(G,-4)=0 for this connected graph and 1 <= 21 < 33,
contradicting the lower-bound conjunct of the complete claim.

## Falsifier

A disconnected graph, a zero only for connected dominating subsets, an
unproved message equality, or a cancellation referring to a different graph
or weight would not establish this refutation. The exact theorem uses the
same graph and ordinary dominating-subset sum throughout, and its conclusion
negates the complete positive claim.

## Evidence

The Lean source contains one public claim definition and one public result
theorem, together with the private graph, decomposition and computational
helpers used by the result. Its claim statement identifier is
sha256:cca7c8c4551c033c05f353ee531ee74845ae6d5fc7885ab8db192ecf2ada7912;
the result identifier is
sha256:7c89cc9aa9923d1a03c53cc00c676590cc52b7a5e52673c0cfe2cb089ebfdd49.

The directly reused zero_of_messages statement identifier is
sha256:ddc1f328c3f47c2b5b892ade2b673ea2aa5668dab47cdda2edb3bb402fbecdeb.
Its restriction/assembly correspondence counts ordinary dominating subsets
once. The result's axiom closure is limited to Classical.choice, Quot.sound
and propext.

The source locator and wording are attributed to arXiv v1. The source has
the arXiv perpetual non-exclusive distribution license; use here is
citation-only. No Creative Commons license is asserted, and no author code
or substantial source prose is reproduced.

## Triage

The external named problem is unit
[#25239](https://github.com/the-omega-institute/trureturing/issues/25239),
with preregistration
[6558891687](https://github.com/the-omega-institute/trureturing/issues/25239#issuecomment-6558891687)
and forecasts 0.60/0.60. The registered refuting event is a connected graph
of some positive order below 33 whose ordinary domination polynomial
vanishes at -4.

The result and private theorem helpers have proof_shape: bind-only after
same-unit expansion. The admission basis is
open-problem-resolution#25239, rather than an escape witness. The utility
is a certified instance refuting the complete claim; the designated
refutation result introduces no additional public audit target.

**What the settlement shows.** The proposed lower bound of 33 is false:
there is a connected 21-vertex, 25-edge counterexample. This does not prove
that 21 is minimal. Published G33 attainment and the distinct item-3
unbounded-family result retain their separate source and result identities.

## ASSUMED-UNVERIFIED

The bounded prior source screen supplies no exhaustive literature or
worldwide-priority conclusion. No independent new literature search is
claimed here. Whether a smaller connected graph has domination root -4
remains outside this result.
