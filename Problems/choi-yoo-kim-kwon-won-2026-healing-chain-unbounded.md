---
slug: choi-yoo-kim-kwon-won-2026-healing-chain-unbounded
bibkey: choi2026healing
doi: 10.48550/arXiv.2610.41277
url: https://arxiv.org/html/2610.41277v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result
---

# Choi–Yoo–Kim–Kwon–Won open problem (1): the healing chain length is unbounded

## Problem

Jeehoon Choi, Suhwan Yoo, Chaeyeon Kim, Hee Young Kwon and Changyeon Won,
“Coordination three heals, coordination four is hard: the antiferromagnetic
Potts model with a costly third state”, arXiv:2610.41277v1, Section VIII,
“Open problems”, item (1):

> The constructive procedure (Proposition 15, Corollary 16) needed at most
> three chain stages in all our tests; is the chain length bounded by a
> constant?

Appendix B defines, for a finite simple graph G, the frustration fr(G) as the
minimum over two-colourings of the number of monochromatic edges,
φ(X) = |X| + fr(G − X), an independent set S as tight when φ(S) = fr(G), and a
tight set T as augmentable when T + v is independent and tight for some v, and
stuck otherwise. Proposition 15 runs, for a connected G ≠ K₄ of maximum degree
at most three and a stuck tight S with fr(G − S) ≥ 1, a chain of single-vertex
exchanges from an odd-cycle component of G − S, testing at each stage the
exchanges T_j − t + y, until one of them is augmentable.

The Lean `claim` states the displacement consequence of a uniform stage bound:
there is C such that for every finite simple connected graph of maximum degree
at most three that is not isomorphic to K₄, and every stuck tight S with
fr(G − S) ≥ 1, some augmentable tight T with |T| = |S| has |S \ T| ≤ C. Every
set the procedure tests at stage j (j = 0, 1, …) differs from S by at most
j + 1 exchanges, so a uniform stage bound would give such a C. The settling theorem
is `result : ¬ claim`.

## Motivation

The ground states of the costly-third-state Potts antiferromagnet on graphs of
coordination at most three are built from an independent odd cycle transversal
of size fr(G); Proposition 15 is the healing step that repairs a stuck greedy
choice. The authors observed at most three stages in their tests and asked
whether that observation is a theorem.

## Gap

Tier 1; preregistration #30587 quotes the question and Appendix B. arXiv lists
only v1; no citing work answering the question was found, MathDB was not
readable and citation indices were rate-limited, so global openness is
ASSUMED-UNVERIFIED.

## Route

For h ≥ 1 take the rooted tree of height h whose root has three children and
whose other internal nodes have two, and replace every node by a triangle; the
root's three vertices and every internal node's two non-apex vertices are
joined to the apices of the children. Every triangle contributes one
monochromatic edge and an explicit colouring attains that bound, so fr(G) is
the number B = 3·2^h − 2 of triangles. The set S of the B − 1 non-root apices
is independent, fr(G − S) = 1, and S is tight and stuck. If T is augmentable
with |T| = |S|, its augmentation meets every triangle exactly once; the root
triangle is met at a port, which forces the child's apex out, and the same
argument descends through a root-to-leaf path, so at least h apices of S are
missing from T. Taking h = C + 1 refutes every proposed C.

## Falsifier

An augmentable tight T with |T| = |S| and fewer than h apices of S missing
would contradict `result`; so would a construction failing one of the
domain conditions (connectivity, maximum degree three, not K₄, tightness or
stuckness of S).

## Evidence

`D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result` has closed type
`¬ claim`. The module imports only pinned Mathlib. Its axiom closure is
contained in {propext, Classical.choice, Quot.sound}; no `sorry`, new axiom or
`native_decide` is used.

## Triage

`theorem`. The proposed uniform bound is refuted, by an infinite family rather
than a finite instance. The admission basis is
`open-problem-resolution (#30587; Refuted)`; the settling descent argument is
content, as is the connectivity proof; the remaining domain and frustration helpers
are consumed bind-only steps.

### What the settlement shows

- [proved: D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result]
  No constant bounds the number of exchanges needed to reach an augmentable
  tight set of the same size, uniformly over connected graphs of maximum
  degree at most three other than K₄. On the tree of triangles of height h
  (B = 3·2^h − 2 triangles, |V| = 3B), every augmentable tight set T with
  |T| = |S| misses at least h apices of S, so at least h exchanges are
  needed, where h = log₂((|V| + 6)/9). Through the bridge of the Problem
  section (a set tested at stage j = 0, 1, … differs from S by at most
  j + 1 exchanges), the first successful stage has index j ≥ h − 1, so at
  least h stages are tested; that bridge is a reading of Proposition 15
  and is not part of the Lean statement.
- [proved: D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result]
  The obstruction is a descent. If T is augmentable with |T| = |S|, its
  augmentation R = T ∪ {v} is an independent set of size B, so it meets
  every triangle exactly once. R meets the root triangle at a port, which
  forces the apex of the adjacent child out of R, and the same argument
  continues along a root-to-leaf path, so at least h apices are missing
  from R; since T ⊆ R, they are missing from T as well. The theorem bounds
  this static displacement; it does not describe the trajectory of
  individual exchanges. The paper's
  upper bound by the number of components of G − S is consistent with this
  family, whose G − S has B components.
- [open] Whether the stage count is bounded on the coordination-three
  lattices on which the authors ran the constructive procedure (truncated
  Penrose tilings, Voronoi foams and the defect honeycomb), or by a function
  of the maximum depth of such odd-cycle trees, is not settled here.
- [open] Planarity is not part of the formal claim; the family is planar, so
  the answer is also negative for planar graphs, but that statement is not
  kernel-checked in this module.

## ASSUMED-UNVERIFIED

- Global openness of the question is `ASSUMED-UNVERIFIED`: arXiv lists only v1, MathDB was not readable and citation indices were rate-limited; the negative search results concern only the recorded scopes.
- Planarity of the counterexample family is not kernel-checked in this module.
