---
bibkey: li2026starprimitive
authors: Will (Ziang) Li
year: 2026
title: Primitives of Holomorphic Functions on Star-Shaped Domains
doi: null
url: https://github.com/will1491/RiemannDynamics/blob/b3fa37cc0f18a23ea66b654ea3f73eb472129010/RiemannDynamics/Hyperbolic/PlaneGeometry/StarShapedPrimitive.lean
claim: "The segment integral is a primitive of a holomorphic function on an open star-shaped complex domain."
strata_touched:
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionSlit
license: Apache-2.0-labelled upstream LICENSE retained verbatim in CompositionContinuation.lean
triage: anchor
---

<!-- GID: D5/L/AnalyticClosure/li2026starprimitive -->
# Li's star-shaped primitive

## Verified locator

Source URL: https://github.com/will1491/RiemannDynamics/blob/b3fa37cc0f18a23ea66b654ea3f73eb472129010/RiemannDynamics/Hyperbolic/PlaneGeometry/StarShapedPrimitive.lean

The source is `will1491/RiemannDynamics` at
`b3fa37cc0f18a23ea66b654ea3f73eb472129010`, file
`RiemannDynamics/Hyperbolic/PlaneGeometry/StarShapedPrimitive.lean`,
lines 1–347. This core has 18,807 UTF-8 bytes and SHA256
`4a6c7dd8f5ee5d90b048e46957df442ae34442e93069979c654b1d937acd4e79`.
It contains `starPrimitive`, `hasDerivAt_starPrimitive`, and four direct
Mathlib imports. Its toolchain is Lean 4.33.0 and its Mathlib revision is
`db584cd6d46c92f209a44c0f1c829460d327499d`, matching this consumer's pins.
The whole upstream package is not imported or admitted.

## License and modifications

The original notice is: Copyright (c) 2026 Will (Ziang) Li. All rights
reserved. Released under Apache 2.0 license as described in the file
LICENSE. Authors: Will (Ziang) Li.

The immutable root LICENSE is 11,319 bytes, SHA256
`44d4b40bd7b0907652947950e63b9aa4379eda788e89eb098fd21e1925612d0d`.
Its complete exact text is retained inside `CompositionContinuation.lean`.
It differs from this repository's LICENSE, including clauses 6 and 9;
the shared Apache label is not a claim of byte equality. The immutable
recursive tree response has `truncated=false` and lists only root LICENSE
among LICENSE, COPYING and NOTICE names; no additional notice chain was found.

Modification notice, 2026-09-22: only the Mathlib-only primitive core is
extracted. The definition is relocated to `CompositionContinuation` and
the proof becomes a local fact inside `CompositionSlit.result`. Upstream
exposition and proof comments are omitted; proof steps are retained.
No lune results, forwarding theorem, new axiom or independent generic
primitive theorem is delivered. The local primitive is used in the live
construction of every nonempty source branch.

Retirement is tied to this repository's own resolved pinned Mathlib:
when it supplies an equivalent star-shaped primitive theorem, use that
declaration directly and retire the redundant transplant. An upstream
submission or acceptance alone does not satisfy this condition.

## Source consumer and attribution boundary

`CompositionSlit.result` constructs the Xu–Zhao branch for every positive
composition on the full slit domain. Nested induction first prepends one,
then raises its exponent by integrating the genuinely removable `dslope`.
The frozen source recurrences and equality at zero identify the disk germ;
analytic identity on the connected slit domain gives both recurrences
and conjugation symmetry globally on that domain.

The primitive theorem is an attributed known supplier, not new mathematics.
The source-specific simultaneous construction is repository-derived.
Neither this reuse nor its continuation consumer resolves Conjecture 1.3.
Solved-problem credit is zero. Pinned Mathlib's `HasPrimitives` supplies disk
primitives and `differentiableOn_dslope` supplies removability; searching
the pinned complex-analysis sources found no equivalent star-shaped
primitive declaration. This is a bounded supplier search, not an exhaustive
claim about all external Lean repositories.
