---
slug: bubboloni-caceres-neighbourhood-upsets
bibkey: bubbolonicaceres2026neighbourhood
doi: 10.48550/arXiv.2608.25912
url: https://arxiv.org/html/2608.25912v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.result
---

# Every upset in a neighbourhood convex geometry is convex

## Problem

Daniela Bubboloni and José Cáceres, *The neighbourhood convexity*,
arXiv:2608.25912v1, “Conclusions and future lines of work,” paragraph
beginning “By exploring the connection with the neighbourhood preorder P(G)”:

> We conjecture that, given a convex geometry (G,n), any upset in P(G) is an n-convex set, having checked it computationally for graphs up to 9 vertices.

For every finite nonempty set $V$ and simple undirected graph $G=(V,E)$,
put $B(x)=\{x\}\cup\{y:xy\in E\}$ and
$N(X)=\bigcap_{x\in X}B(x)$, with $N(\varnothing)=V$.
Let $C=\{N(Y):Y\subseteq V\}\cup\{\varnothing\}$, let
$h(\varnothing)=\varnothing$ and $h(X)=N(N(X))$ for nonempty $X$, and put
$\operatorname{ex}(K)=\{x\in K:K\setminus\{x\}\in C\}$.
Assume $h(\operatorname{ex}(K))=K$ for every $K\in C$.
Then, for every $U\subseteq V$,

$$
\left(\forall x\in U,\ \forall y\in V,\ B(x)\subseteq B(y)\Rightarrow y\in U\right)
\Rightarrow U\in C.
$$

The source anchors are Sections 2.1 and 2.2, Definitions 3, 5, 9 and 28,
and Proposition 12. The quantifiers include all positive graph orders,
disconnected graphs, universal vertices, equal closed neighbourhoods and the
empty upset. No connected, star-free or twin-free hypothesis is substituted.

## Motivation

Lemma 29(iii) already supplies convex principal upsets, and Lemma 29(iv)
supplies the converse implication from convex sets to upsets. Proving the
conjecture identifies the whole convex family with the upset family of the
neighbourhood preorder, rather than only its principal members.

## Gap

The external exact target is preregistered in issue #12622. The source and
literature qualification reports no exact supplier in canonical D5, including
private declarations, pinned Mathlib, or the examined third-party sources.
The latest-version arXiv id-list query returned v1. Exact-title and
paired-author arXiv metadata queries returned only this paper; each of two
bounded Crossref queries examined 20 records and found no exact title match.
All-state repository ownership searches found only issue #12622 for this
target. These findings are confined to those search scopes.

Classical finite convex-geometry and meet-distributive-lattice results, such
as Czédli, arXiv:1208.3517v3, Proposition 2.1 and Section 7, provide context.
They are not treated as an already published exact resolution of this graph
conjecture, and no classical source proposition is assumed in the Lean proof.

## Route

Let $L$ be the image of $N$ and $S=N(V)$. Symmetric incidence gives
antitonicity, extensivity of double polarity and the triple-polarity identity.
Thus $N$ is an order-reversing involution on $L$.

The full extreme-point hypothesis gives a deletable point outside any proper
convex subset. Every cover in $L$ consequently changes one vertex; polarity
transports covers to covers. Deletion induction starting at $S$ gives

$$ |K|+|N(K)|=|V|+|S|\qquad(K\in L). $$

For $A,B\in L$, apply this identity to $A$, $B$, $A\cap B$ and
$J=N(N(A\cup B))$. Inclusion-exclusion and
$N(A)\cup N(B)\subseteq N(A\cap B)$ give $|J|\le|A\cup B|$.
Extensivity gives the reverse inclusion, so $J=A\cup B$ and actual unions
are closed. Adding the empty set preserves union closure. The local proof
of the published principal-upset identity and finite union formation now
produce every upset.

## Falsifier

A refutation would require one actual finite nonempty simple graph satisfying
$h(\operatorname{ex}(K))=K$ for every $K\in C$, together with an upset outside
$C$. Failure of union closure without the geometry hypothesis is insufficient.
Replacing the hull at the empty set by double polarity, or assuming the rank
identity or union closure, would change the target or leave the proof incomplete.

## Evidence

The canonical Lean module is
`D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.lean`.
It contains the five necessary definitions and one public theorem, `result`.
All intermediate arguments are local have blocks inside that theorem.
The exact theorem proves the implication for an arbitrary finite nonempty
vertex type and arbitrary simple graph, with the full geometry hypothesis.
Its proof uses `propext`, `Classical.choice` and `Quot.sound` only.
The source's computations through nine vertices are not used as evidence.

## Triage

Tier 1: a recent explicit finite-graph conjecture, preregistered before any
local proof probe. Proposed admission is `open-problem-resolution`.
The producer classifies the actual proof as `content`: deletion induction
and dual unit covers establish rank complement, and the resulting cardinal
inequality forces union closure. Utility is `none`, because the delivered
result is universal structural mathematics, not finite enumeration, a
checker, numeric reduction or certified instance. Independent source-fidelity,
term-classification and mirror review remain delivery boundaries.

**Proved inside the exact Lean result:** the rank-complement identity on $L$,
actual binary union closure in $L$ and $C$, and convexity of all upsets under
the full geometry hypothesis. The rank identity is not claimed for the extra
empty set when $S$ is nonempty. Neither universal vertices nor disconnected
graphs are excluded.

**Source consequence:** together with published Lemma 29(iv), the proved
implication identifies neighbourhood-convex sets with all upsets in the
neighbourhood preorder. This converse is cited rather than separately
packaged as a new theorem. The already published principal-upset assertion
is a prerequisite, not a new independently delivered result.

**Open:** the paper's separate extreme-point conjecture. No implication
settling it is established by this result, and no additional companion
claim is included. Extensions beyond symmetric closed-neighbourhood incidence
or beyond the full extreme-point generation hypothesis remain unproved here.

## ASSUMED-UNVERIFIED

The bounded literature qualification does not exclude unindexed or unpublished
work, unread related full texts, unknown later resolutions, or establish
global novelty or priority. General web searches supplied no usable exclusion
evidence. The source quotation, version and search findings are external
qualification evidence; Lean does not authenticate publication history.
The result is a project proof of the cited assertion, not a claim that the
original paper published a settlement.
