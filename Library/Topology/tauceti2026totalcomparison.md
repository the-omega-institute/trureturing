---
bibkey: tauceti2026totalcomparison
authors: The Tau Ceti contributors; Claude (extension-homology support)
year: 2026
title: First-quadrant row-to-total quasi-isomorphism comparison
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/TotalComplex.lean
claim: Every rowwise quasi-isomorphism of first-quadrant chain bicomplexes in an arbitrary abelian category induces a quasi-isomorphism of the actual native total complexes.
strata_touched:
  - D5/S3/Topology/TauCeti/Algebra/Homology/TotalComplex
license: Apache-2.0
triage: anchor
---

# First-quadrant row-to-total comparison

The immutable source is TauCetiProject/TauCeti revision
`580580ea8726c50dcf98e199fa0a7caef5a74302`.
The selected text is `TauCeti/Algebra/Homology/TotalComplex.lean`,
lines 80–87 and 243–586, SHA-256
`103c74dcfb667bf8d634bb95ba84dab64207661ff984e3a4fa08fc5b3a1b6bb4`.
Consumed middle-map support is from `HomologySequenceLemmas.lean`,
lines 73–126, full-file SHA-256
`7ee5191eb88a89e2be916e69ada1e5d3e325354e7584bd919dd4be8acabf3d40`.
Consumed extension support is from `Embedding/ExtendHomology/Basic.lean`,
lines 64–82, full-file SHA-256
`04c064e82d2cf8ea7b679392130fc444b22e5f4b53c1dab62540917612fd4a1a`.
The latter file attributes its authorship to Claude and cites
https://github.com/TauCetiProject/TauCeti/pull/10141.

The source pins Lean 4.36.0-rc1 and Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`; the receiving library pins
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The unequal pins require selective source adaptation rather than a direct
package dependency. The retained construction consists of row-zero inclusion,
positive-row quotient by extension along `n ↦ n+1`, natural antidiagonal
splitting, the simultaneous cutoff induction and the exact comparison theorem.
Native finite-antidiagonal, total-map, extension-homology and homology-diagram
interfaces are reused. Auxiliary declarations are private. Augmentation,
symmetry and singular-chain subtrees are omitted.

The telescope has independent object and morphism universes, every abelian
category, every first-quadrant bicomplex and its actual morphism. Rowwise
quasi-isomorphism implies quasi-isomorphism of the native total map in all
natural degrees including zero. No AB4, finite support, finite length,
nonemptiness, coefficient field, supplied convergence or contraction is assumed.
The native total differential is `d1 + (-1)^p d2`. The positive-row quotient
preserves p and uses extension by zero, not a signed suspension.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors.
The extension support also retains: Copyright (c) 2026 Tau Ceti contributors.
All rights reserved. Authors: Claude.
Released under Apache 2.0 license as described in the file LICENSE.
The full license is retained in
[the Tau Ceti license](../../docs/reports/licenses/tauceti-sphere-port-LICENSE.txt),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The supplied immutable-tree license check found no NOTICE file.
The receiving Lean source retains attribution and a modification notice.

The source cites C. A. Weibel, *An Introduction to Homological Algebra*,
Section 2.7, for acyclic assembly. That is the source's bibliographic pointer;
no independent reading of the book, priority, originality or first-Lean claim
is made. The pinned Lean text is the source used here.

## Retirement

Replace this adaptation when the receiving project's own pinned library
provides the equivalent complete telescope and actual native total map,
and direct replacement checks discharge its mathematical consumers.

## Verified locator

https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/TotalComplex.lean#L539-L586
