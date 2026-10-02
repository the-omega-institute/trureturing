---
bibkey: bertuzzo2026coveragedepth
authors: Matteo Bertuzzo, Alberto Ravagnani, Eitan Yaakobi
year: 2026
title: "The DNA Coverage Depth Problem: Duality, Weight Distributions, and Applications"
doi: 10.48550/arXiv.2603.06489
url: https://arxiv.org/html/2603.06489v1
claim: "Section 3 Conjecture 3.2 asks whether the q-ary simplex code attains minimum actual iid uniform physical-column full-recovery expectation at n=(q^k-1)/(q-1)."
strata_touched:
  - D5/S3/Resource/SimplexCoverageOptimality
license: citation-only
triage: anchor
---

# Simplex coverage depth and optimality

## Exact sources

The primary source is arXiv:2603.06489v1, Section 2 (Problem B and
the rank-k generator convention), and Section 3, Conjecture 3.2.
The predecessor is arXiv:2507.20639v1, Section III, the unnumbered
paragraph conjecturing simplex optimality. Both versioned source texts
are directly checked. Preregistration is
https://github.com/the-omega-institute/trureturing/issues/11799.

## Known source facts

Problem B minimizes the expected first full-span retrieval time among
all dimension-k linear codes of fixed length n over a finite field of
cardinality q. Physical generator-column positions are drawn uniformly,
independently and with replacement. The standing scope is k at least
two. A generator has rank k; zero, repeated and scalar-parallel columns
are not excluded by that convention.

A simplex generator has one nonzero representative of each projective
line and length n=(q^k-1)/(q-1). The source's Theorem 3.1 already gives
its expectation as

$$
k+\sum_{i=1}^{k}\frac{q^{i-1}-1}{q^k-q^{i-1}}.
$$

This formula is a published fact, not a repository novelty or a second
settlement. Conjecture 3.2 asks whether the simplex code achieves
Problem B's minimum at these exact parameters.

## Repository full proof

The sole formal handle is
`D5/S3/Resource/SimplexCoverageOptimality.result`. It quantifies arbitrary
finite field structures, every k at least two, every actual rank-k
Matrix (Fin k) (Fin n) K competitor, and every physical simplex matrix
whose ray map is bijective. The conclusion compares the real integrals
of the original `MinimumRetrievalTime.retrievalTime` toReal under
`MinimumRetrievalTime.uniformSamples (Fin n)`. It has no extra
concavity, invariance, positive-mass, integrability or finiteness
assumptions. The simplex's full span is proved, not assumed.

The proof replaces only competitor zero columns on the same positions,
proves prefix-span and global-span containment, applies represented
polynomial root concavity through local GL orbit averaging and local
physical fiber sums, and identifies projective sampling with the
actual physical simplex alphabet. Measurable complements compare all
failure tails, and the frozen actual-expectation bridge compares their
ENNReal sums before converting the finite original expectation to real.
The routine projective and physical deductions have no separate retained
formal handles.

The full result is kernel-checked with axiom closure exactly
`propext`, `Classical.choice`, `Quot.sound`. It is a bind-only proof
admitted as a complete preregistered named open-problem resolution,
not an escape-witness result. Independent admission and publication
are separate from this mathematical evidence.

## Search and priority boundary

The completed supplier map covers the pinned repository retrieval,
represented polynomial and probability interfaces and the relevant
Mathlib projectivization, finite Jensen, cylinder and ENNReal order
interfaces. The map is bounded, not an exhaustive repository-equivalence
or literature-priority search. This proof reuses those interfaces and
the local projective/fiber deductions rather than rediscovering them.

The primary and predecessor versions retain the optimizer conjecture.
Bounded independent readings also checked arXiv:2608.20152v1,
2609.36067v1, 2601.07053v2 and 2507.20645v1. In particular,
Section VI of 2601.07053v2 treats full recovery: its Theorems 4 and 5
and Corollary 6 provide bounds and asymptotics, rather than the exact
universal simplex optimizer. The checked sources do not supply a
dominating full resolution. This is not an exhaustive global priority
certificate; unindexed work and inaccessible final publisher revisions
remain unverified. Canonical admission, freezing and merged delivery
are separate repository facts, not consequences of the theorem alone.
