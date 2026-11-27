---
slug: hu-han-2026-signed-square-energy-equality
bibkey: huhan2026signedsquareenergy
doi: 10.48550/arXiv.2608.18492
url: https://arxiv.org/abs/2608.18492v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.result
---

# Equality at both signed square-energy endpoints

## Problem

Fu-Tao Hu and Xiao Han ask in Problem 6.1 for all connected signed simple graphs
with $s^+ = 2m-n+1$ and all with $s^+ = n-1$, up to switching and
isomorphism. Here $n$ is the vertex count, $m$ is the unordered edge count,
and $s^+$ sums squares over every positive adjacency eigenvalue occurrence.
[Source v1](https://arxiv.org/html/2608.18492v1#S6.Thmtheorem1)
[Preregistration](https://github.com/the-omega-institute/trureturing/issues/33287)

## Motivation

For complete graphs on at least three vertices, the two numerical equalities
select distinct switching classes. On $K_2$, the all-positive and all-negative
signings are switching-equivalent, so the two classes coincide. Classifying both
also identifies every connected signed graph for which the Hu–Han bound is strict
at either endpoint.

## Gap

Hu–Han prove the bounds and give the attaining examples. The unsigned
classifications of Hu–Liu–Wang, Theorem 1.1, also determine the balanced and
antibalanced specializations using conservation, switching and sign reversal.
Liu–Tang–Zhang supply the earlier matrix inequality and unsigned square-energy
bound. The bounded literature screen in the preregistration and source
qualification found no complete answer for arbitrary signings among the related
papers, indexed citations, and targeted source and theorem searches it inspected.
The external automath record contains a candidate brief for the exact question.
Its outcome and priority beyond the inspected sources remain unverified.
[Unsigned classifications](https://arxiv.org/abs/2608.17329v1)
[Earlier bound](https://arxiv.org/abs/2607.18031v1)
[Candidate brief](https://github.com/chy4pro/automath/blob/5542184180d014b68637851941109dd5e584e920/engine/briefs/mining_r1/check/chk_024.md)

## Route

`D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.result` proves the
conjunction of the two equivalences. Signed trees occur in both. For a complete
graph the upper endpoint requires switching from the all-positive signing and
the lower endpoint requires switching from the all-negative signing. Relabeling
by `Fin n` covers any finite carrier. In the singleton case the signing is
irrelevant and $s^+=0$ equals both bounds.

At the upper endpoint the folded square of the positive spectral part attains
the normalized matrix equality of Hu–Liu–Wang, Proposition 4.3. Zero-sum
extensions from a root clique force cross-fiber nonedge entries of the positive
part to vanish. Commuting the positive part with signed adjacency rules out all
attachments to a block of size at least three. If every block is an edge, the
graph is a tree. For a complete graph the positive part forces a rank-one sign
pattern. Bipartite spectral symmetry proves attainment for signed trees, and
the rank-one projection gives attainment for balanced complete graphs. Sign
reversal and conservation give the lower equivalence.

## Evidence

The source is `D5/S3/Combinatorics/SignedGraphSpectral/HuHanSquareEnergy.lean`.
Its settling declaration is `result`. The proof directly uses the signed
adjacency and Hermitian witness owned by MO479815, the Brooks cut partition,
and the Hermitian positive-part calculus in `RHLinalg`.

A Codex CLI search seat proposed the signed paper argument. A separate Codex CLI
reviewer independently compared the source statement, proof, prior art and Lean
route.
[Preregistration and sign-reversal conservation](https://github.com/the-omega-institute/trureturing/issues/33287#issuecomment-7081959562)

## Falsifier

A missing direction of either equivalence, a restriction on admissible edge
signs, a change to the adjacency or spectral multiplicities, or an exclusion of
the singleton would fail to settle the problem as stated.

## Triage

### What the settlement shows

The upper and lower equality classifications hold for every connected finite
signed simple graph. On a connected underlying graph that is neither a tree
nor complete, both endpoint inequalities are strict by the Hu–Han bounds.
On a complete graph, the two cases select the indicated uniform signing up to
switching. The exact selected declaration is the conjunction of the two
equivalences.

## ASSUMED-UNVERIFIED

The bounded prior-art comparison leaves unindexed, unpublished, and later
results outside the inspected sources.
