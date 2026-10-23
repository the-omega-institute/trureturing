---
bibkey: gleason1958projective
authors: Andrew M. Gleason
year: 1958
title: Projective topological spaces
doi: 10.1215/ijm/1255454110
url: https://projecteuclid.org/euclid.ijm/1255454110
claim: Compact Hausdorff projective spaces are exactly the extremally disconnected spaces.
strata_touched: []
license: citation-only
triage: anchor
---

# Projective compact Hausdorff covers and dynamics

Gleason, *Illinois Journal of Mathematics* 2, pp.482–489, Theorem 2.5,
characterizes projective compact Hausdorff spaces by extremal
disconnectedness. A space is extremally disconnected when the closure
of each open set is open. Projectivity guarantees continuous lifting
through compact Hausdorff surjections. It does not assert shadowing of
the lift.

The pinned Mathlib module `Mathlib.Topology.ExtremallyDisconnected`
attributes and proves this characterization as
`CompactT2.projective_iff_extremallyDisconnected`; its direction
`CompactT2.Projective.extremallyDisconnected` is enough for the exclusion
below. Its definition and closure lemmas, together with the repository's
`finite_observation_isSofic`, supply the prior machinery for
`D5/S1/Dynamics/Shadowing/StoneanForwardTubeObstruction`.

For the successor map on the compact convergent sequence of natural
numbers, every compact Hausdorff projective cover with any continuous
equivariant lift fails shadowing. The isolated-point fibers are nonempty
disjoint open forward tubes; extreme disconnectedness supplies their
arbitrary clopen coloring, while shadowing would force a finite graph
observation language. The power-of-two coloring contradicts that graph
language by whole-path cycle erasure. The exact proof and its boundary
are in the owning problem dossier and Blueprint.

This is a construction obstruction, not a negative answer to Peng's
Question 5.1: the convergent-sequence source itself is a zero-dimensional
shadowing cover. No attribution of this dynamic obstruction to Gleason,
and no worldwide novelty claim for it, is made.

## Verified locator

Gleason, *Projective topological spaces*, Illinois J. Math. 2, pp.482–489,
Theorems 1.2 and 2.5.

- DOI: https://doi.org/10.1215/ijm/1255454110
- Publisher: https://projecteuclid.org/euclid.ijm/1255454110
