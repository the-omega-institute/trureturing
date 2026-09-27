---
slug: mamede-santos-soares-2026-conjecture-five-one
bibkey: mamede2026commutation
doi: 10.48550/arXiv.2601.09395
url: https://arxiv.org/html/2601.09395v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Permutations/MamedeDeletionEquiv
---

# Mamede--Santos--Soares Conjecture 5.1

## Problem

Conjecture 5.1 states: for every $n\geq1$ and every permutation
$\sigma\in S_{n+1}$, $|R_\bullet(\sigma)|\in\{0,1,2,4\}$.
Here $R_\bullet(\sigma)$ is the set of one-element commutation classes of
reduced adjacent-transposition words. The paper's Theorem 3.9 proves the
upper bound four; the remaining assertion excludes exactly three classes.
The paper identifies these classes with reduced words whose successive
generator indices differ by one, as in the repository's `singletonWord`.
The source is [Section 5 of arXiv:2601.09395v1](https://arxiv.org/html/2601.09395v1#S5).

## Current result

`MamedeDeletionEquiv.source_deletion_equiv` gives a first-orientation
equivalence of actual singleton-word fibers under `exactSourceHypotheses`.
Its forward map deletes part of the forced excursion and reduces length by
the positive, fixed length of `deletedExcursion`. The existing
`source_shape_for_every_singleton` and `source_deletion_surjective` provide
the all-source shape and onto directions. This is a conditional count-preserving
step, not a verified resolution of Conjecture 5.1. KPI: 0.

## Gap

The reflected orientation, oscillating and involutive branches, and a global
count argument for every permutation remain unproved. The induction also needs
to derive the exact endpoint and exterior hypotheses from an arbitrary
nonoscillating source, up to reflection, and handle the terminating cases.
The class-to-word correspondence and the paper's upper bound still require
formal justification in this adjacent-word model before the full conjecture
can be claimed. Research target: [#10285](https://github.com/the-omega-institute/trureturing/issues/10285).
