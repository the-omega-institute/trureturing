---
bibkey: klukowski2024congruence
authors: Adam Klukowski
year: 2024
title: Congruence subgroup property for nilpotent groups and subsurface subgroups of Mapping Class Groups
arxiv: 2411.06867v2
claim: Finite characteristic quotients define congruence subgroups; the paper proves congruence separability for solvable subgroups and formulates a curve-orbit congruence-control conjecture.
strata_touched:
  - D5/S3/Observer/Dynamics/SurfaceTwistCongruence
license: citation-only
triage: anchor
---

# Surface congruence and finite nonabelian observations

Primary source read: https://arxiv.org/html/2411.06867v2

## Exact scope

Definition 3 uses a finite characteristic quotient of a group G and the induced
map on Out(G) to define congruence subgroups. Corollary 7 already proves
congruence separability of solvable subgroups of a mapping class group.
Theorem 8 controls inclusion of subsurface subgroups. Corollaries 10 and 11
handle stabilizers of sufficiently large multicurves and their intersections
with principal congruence kernels.

Conjecture 13 asks: for any finite-index subgroup Gamma of Mcg(Sigma) and any
simple closed curve alpha, does a congruence subgroup Delta exist with
Delta.alpha contained in Gamma.alpha? The current bounded search did not find
a resolution of this general statement. This does not establish exhaustive
priority or rule out unpublished work. Genus at least three is the unsolved
CSP horizon in Conjecture 1; known low-genus CSP is not a new target.

Lemma 14 is a known composition lemma. It requires both the restricted CSP
and a congruence condition for all finite-index subgroups containing the
selected subgroup. Detecting all powers of one separating twist does not
supply the second premise or prove Conjecture 13.

## Relation to the explicit construction

The new source uses the actual genus-(extra+2) presentation and constructs a
finite fully invariant quotient as the image of evaluation at all maps to a
dihedral group of order 8m. It proves the exact outer period m of the chosen
partial-conjugation automorphism. Its lower bound compares two generator
images under one common conjugation; its upper bound works for every map to
the target. This note does not attribute the particular 8m target or the
matching explicit formula to a numbered result of Klukowski.

The qualitative consequence for the cyclic twist subgroup is classical and
already covered by broader known congruence results. It is not an external
open problem solved here. The proof source is a candidate construction, not
a claim of mathematical first discovery or repository admission.

## Other primary context

- Wilton and Sisto, *The congruence subgroup property for mapping class groups
  and the residual finiteness of hyperbolic groups*, arXiv:2410.00556.
  https://arxiv.org/abs/2410.00556 . The general CSP conclusion assumes residual
  finiteness of every hyperbolic group; that premise is not available here.
- Boggi, *A congruence subgroup property for symmetric mapping class groups*,
  arXiv:2408.12486. https://arxiv.org/abs/2408.12486 . Its centralizer result
  assumes quotient-surface genus at most two. It is not an unconditional
  solution for all higher-genus mapping class groups.

## Bounded source and implementation audit

2026-09-14: read the sources above and searched separating-twist/dihedral and
mapping-class CSP combinations. Repository searches for SeparatingTwist and
Klukowski returned no matching owner. Generic surface results mainly concerned
engineering surfaces. Read the merged #7614 disposition: its nine previous
candidate Lean modules were withdrawn; none is imported here. No claim that
all open PRs or all external libraries were searched is made.

The only proof upstream is mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Read the actual
`GroupTheory/PresentedGroup.lean` and `SpecificGroups/Dihedral.lean` APIs.
No existing exact canonical-quotient/outer-order theorem was located in this
bounded search. Finite diagnostics check group operations, the relator,
repeated twists and simultaneous conjugacy; they do not certify Lean
elaboration, whole-kernel invariance or unbounded quantifiers.
