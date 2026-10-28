---
bibkey: klanderman2026generalizedactiongraphs
authors: S. Klanderman, K. McDicken, A. Tebbe
year: 2026
title: Conditions for Building Generalized Action Graphs From Sequences
doi: 10.46787/pump.v9i.6304
url: https://journals.calstate.edu/pump/article/view/6304
claim: "Another open question is whether the hypotheses of Theorem 1.1 are in fact necessary conditions for generalized action graphs to exist."
strata_touched:
  - D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity
license: citation-only
triage: anchor
---

# Generalized action graphs and strictly positive convolution coefficients

S. Klanderman, K. McDicken and A. Tebbe, *Conditions for Building Generalized
Action Graphs From Sequences*, The PUMP Journal of Undergraduate Research
9 (2026), 158–179. The governing question is Section 4, page 178, quoted in
the claim field. The earlier version is arXiv:2507.22861v1, where Definition
4.1, Theorem 2.1 and Section 6 correspond to the journal's Definition 1.1,
Theorem 1.1 and Section 4. These are versions of the same question.

## Verified locator

DOI: 10.46787/pump.v9i.6304
Source: https://journals.calstate.edu/pump/article/view/6304

Published journal version, pages 158–179: Definition 1.1 (pages 158 and 172),
Theorem 1.1, and the Section 4 question (page 178).

## Source definition and theorem

Definition 1.1, pages 158 and 172:

> The sequence Gn of generalized action graphs for a particular sequence sn
> of positive integers is a sequence of directed, labeled, rooted trees such that:
> Axiom 1 Define G0 as the graph with s0 vertices labeled 0 and no edges.
> Construct Gn from Gn−1 by adding sn new vertices, which are each labeled n.
> Axiom 2 For vertex v in Gn, the subtree of Gn with root v is isomorphic to
> some Gk such that k ≤ n.
> Axiom 3 All leaves in the graph Gn have label n.

The paragraph following the repeated definition on page 172 specifies:

> Note that subtree of G with root v here means the subgraph of G consisting
> of all descendants of v and edges between them in G.

Section 3.1, page 172:

> Note that when we consider isomorphism in generalized action graphs, the
> labels on the vertices may be shifted, but the underlying structure of the
> graphs are the same.

Theorem 1.1 assumes positive integers s(n) for n ≥ 0 and z(i) for i ≥ 1,
s(0) = 1, and s(n) = Σ(i=1,…,n) z(i)s(n−i) for every n ≥ 1. It constructs
generalized action graphs at every stage. Its additional conclusion identifies
z(i) with root-adjacent vertices of label i and gives shifts upward by i.
Definition 1.1 does not require strictly positive root multiplicities of every
label. The Section 4 question asks whether the theorem's hypotheses are
necessary; the strict positivity of every z(i) is part of this question.

## Mathematical scope

The constant sequence s(n) = 1 has the candidate family of directed paths
0 → 1 → ⋯ → n, rooted at 0 and with each vertex labeled by its index.
The descendants of i form the suffix i,…,n. Translation j ↦ i+j identifies
that induced rooted subgraph with the path of length n−i, shifting every
label upward by i. The convolution at n=1 gives z(1)=1, and at n=2 gives
1=z(1)+z(2), hence z(2)=0. This argument concerns the strictly positive
necessity question. It supplies no refutation of a nonnegative-coefficient
variant. The authors pose the question; they do not assert this negation.

## Source and literature limits

The journal galley is
https://journals.calstate.edu/pump/article/download/6304/5451?inline=1.
The supplied full-text extraction has SHA-256
`5b703bc87df86fc85755cd11a3b29f1dcaab2321950ccb332ccb014deb51988c`.
The bounded source, version and citation checks supplied with the target
found no complete earlier settlement. Failed or rate-limited sources supply
no negative evidence. No exhaustive novelty or priority claim follows.
Caldwell and coauthors' arXiv:2507.22719 Conjecture 5.6 concerns the specific
super Catalan action-graph path table and is a different question.
