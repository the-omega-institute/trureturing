---
bibkey: lyng2026danskin
authors: Daniel Lyng
year: 2026
title: "Econlib Danskin directional derivative of a compact envelope"
doi: null
url: https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Math/Analysis/Danskin.lean
claim: "A jointly continuous compact envelope with convex parameter fibers has a right directional derivative attained at an optimizer and dominating the directional derivatives at all optimizers."
strata_touched:
  - D5/S3/Analytic/Convexity/Danskin
license: Apache-2.0 source
triage: anchor
---

## Source and scope

The proof supplier is Daniel Lyng's `Danskin.hasRightDirDeriv_iSup` in
`Econlib/Math/Analysis/Danskin.lean`, lines 239–439, at immutable revision
`d7bd9477476cade1c6695c8891746048ceddc52f`. The source theorem and its consumed
support closure are extracted faithfully. The project header, imports and
module visibility syntax are adapted; no Optlib code is retained. This is
attributed reuse of an upstream proof, with no claim of new mathematics.

The parameter space is a real inner product space, the index space any
nonempty compact topological space, and the parameter domain open and convex.
The family is jointly continuous on that domain times the whole index space
and convex in each parameter fiber. Existence of each optimizer's directional
derivative implies existence of the envelope's right directional derivative,
attained at one optimizer and dominating every optimizer derivative. No
completeness of the parameter space, separation axiom on the index space,
or uniqueness of an optimizer is assumed.

The source copyright and authorship are retained in the Lean module. The
complete Apache-2.0 license is retained at
`docs/reports/licenses/econlib-Danskin-LICENSE.txt`, SHA-256
`0d542e0c8804e39aa7f37eb00da5a762149dc682d7829451287e11b938e94594`.
The compact scalar Strassen construction in `lyng2026compactstrassen` is a
different theorem and is not the source of this result.

For continuous real functions b and h on a nonempty compact subset K of an
arbitrary topological space, the compact subtype K and the affine family
b(z)+t*h(z) give the one-sided extremum formulas discussed in the owning
Blueprint Scribe. These are applications of the cited theorem, preserving
all tied optimizers and introducing no finiteness or metric assumption.

Retirement requires an equivalent declaration at this repository's own
resolved Mathlib pin, with the full original telescope and the attaining and
dominating conclusions, together with direct compact-subtype affine
applications proving both literal right maximum and minimum little-o
expansions without additional premises. Upstream acceptance alone does not
satisfy this condition.
