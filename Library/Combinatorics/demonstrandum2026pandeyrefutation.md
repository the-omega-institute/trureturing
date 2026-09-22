---
bibkey: demonstrandum2026pandeyrefutation
authors: demonstrandum-research/artifacts (repository publisher)
year: 2026
title: "Refutation of the Parity Conjecture for Independence Polynomials of Generalized Petersen Graphs (arXiv:2601.03293, Conjecture 4.1)"
doi: null
url: https://github.com/demonstrandum-research/artifacts/blob/94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3/problems/p2-factory/kills/pandey-parity/WRITEUP.md
claim: "Prior full refutation of Pandey's Conjecture 4.1: GP(3,1) has real-rooted independence polynomial 1+6x+6x^2 with odd step, and the explicit isomorphism GP(7,2) to GP(7,3) contradicts the universal parity biconditional."
strata_touched:
  - D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation
license: citation-only
triage: anchor
---

# Prior public refutation of Pandey's Parity Conjecture

## Verified locator

URL: https://github.com/demonstrandum-research/artifacts/blob/94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3/problems/p2-factory/kills/pandey-parity/WRITEUP.md

The title and URL above identify the public `WRITEUP.md` in
`demonstrandum-research/artifacts`. The `authors` field identifies its
publishing repository, not a verified personal author. No DOI or external
license is established here; `citation-only` describes this Library note's
use of the source and makes no claim about the source's license.

The immutable commit is `94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3`,
with provider-reported author and committer timestamp
`2026-06-13T01:23:03Z`. The exact file blob is
`a82a8fe898b3ecb7dc94608f32cb2cf97ce4cc1e`, and its bytes have SHA-256
`2c5af094fda2424c95bd47ca3ef2cfba7dbbcfd4a74039ae963c367769881fe1`.
The internal June 11 date is unverified and is not used as the public
provenance date.

## Exact prior refutation

The graph domain and conjecture are recorded in the separate
[Pandey Library note](pandey2026parity.md): `n >= 3`, `1 <= k`,
`2*k < n`, with no restriction to the experimental range `20 <= n <= 30`.
Section 3(c) of the prior note explicitly gives the triangular prism
`GP(3,1)`, its polynomial `1+6x+6x^2`, and its real-rootedness although
`k=1` is odd. This is the exact counterexample formalized locally.

Section 3(d) gives `GP(7,2) -> GP(7,3)` by
`u_j -> v'_(3j mod 7)`, `v_j -> u'_(3j mod 7)`. Multiplication by 3 is
invertible modulo 7. Outer edges map to step-3 inner edges, step-2 inner
edges map to outer edges with step `6 = -1 mod 7`, and spokes map to
spokes. Both parameter pairs satisfy the source domain. Thus the graphs
are isomorphic and have equal independent-set counts and polynomials,
while their steps have opposite parity. The full universal biconditional
would assign contradictory real-rootedness predictions to this same
polynomial. This argument needs no computed roots and already refutes
the full assertion. The source's additional numerical, enumeration,
Sturm, checker, and audit claims are not verification evidence adopted here.

## Local formalization and attribution

The [problem dossier](../../Problems/pandey-parity-conjecture-refutation.md)
and [canonical Blueprint](../../Blueprint/D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.md)
record the local Lean formalization of the known `GP(3,1)` refutation,
not a formalization of the source's other counterexamples or isomorphism.
The result's structured literature citation refers to this note; the
graph and conjecture retain Pandey provenance.

The prior exact resolution supersedes the bounded no-hit literature
screen for [issue 8619](https://github.com/the-omega-institute/trureturing/issues/8619)
and invalidates the historical `open-problem-resolution` novelty-admission
basis. This is not an eligible newly solved open problem. The conservative
`proof_shape: bind-only` assessment remains; no replacement admission
basis or escape witness is asserted. The valid frozen mathematics is
retained under CLAUDE §§1.3 and 3.2. Under spec §11.20.5, the typed
`Refuted` record binds the local theorem to the problem without claiming
worldwide novelty. Literature completeness beyond this exact hit is
`ASSUMED-UNVERIFIED`; no earliest-priority claim is made.
