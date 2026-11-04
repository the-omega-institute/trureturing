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
  - D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison
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
The embedding binding also corresponds to `Embedding/DownNatSucc.lean`,
lines 27–35, full-file SHA-256
`11fcdd12fb381b23df8335d545a6f31f8a5b716a01deeda00a63f128617d98bb`.
It directly uses the receiving `ComplexShape.embeddingDown'Add (1 : ℕ) 1`.
The extension-support file attributes its authorship to Claude and cites
https://github.com/TauCetiProject/TauCeti/pull/10141.

The source pins Lean 4.36.0-rc1 and Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`; the receiving library pins
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The unequal pins require selective source adaptation rather than a direct
package dependency. The retained construction consists of row-zero inclusion,
positive-row quotient by extension along `n ↦ n+1`, natural antidiagonal
splitting, the simultaneous cutoff induction and the exact comparison theorem.
Native finite-antidiagonal, total-map, extension-homology and homology-diagram
interfaces are reused. The local epi and isomorphism homology-transfer lemmas,
extension-homology transport lemmas, successor embedding, row-reindexing
morphism, natural short-complex morphism and short-exactness theorem are
public for finite-degree comparison. The remaining auxiliary declarations
are private. Augmentation and singular-chain subtrees are omitted.

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

## Finite-degree comparison and total symmetry

The finite-degree comparison uses the same row-zero short exact sequence and
local homology-transfer statements with triangular, rather than whole-row,
homology hypotheses. For every natural k, isomorphisms of actual column
homology at p+q at most k and epimorphisms at p+q=k+1 imply isomorphisms of
native total homology through k and an epimorphism at k+1. The bounded
induction is composed in the receiving source. This is a standard general
comparison theorem; no literature novelty or first-formalization claim is
made for that composition.

The consumed Nat total-symmetry instance is from TauCetiProject/TauCeti
revision `289eb81f25e69d47485b9ab90980e873372581d4`,
`TauCeti/Algebra/Homology/ComplexShape/Signs.lean`, SHA-256
`aa2f70d120656d777296a3bcfe00ff2d6c3a0630b5cf3823cf7430fa65e8228c`:
https://github.com/TauCetiProject/TauCeti/blob/289eb81f25e69d47485b9ab90980e873372581d4/TauCeti/Algebra/Homology/ComplexShape/Signs.lean
It supplies the sign (-1)^(p*q) for the pinned Mathlib `totalFlipIso`.
Only its instance is retained, privately, with its original implementation
and contributor notice. The source pins Lean 4.36.0-rc1 and Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`; the receiving pins are stated
above. Its Apache-2.0 license has the same retained license SHA-256 stated
above. This coordinate and sign adaptation supplies no new mathematical
content claim.

## Homological nerve application

Patrick Gillespie, *A homological nerve theorem for open covers*,
arXiv:2210.00388v1, Theorem 1, supplies the published conclusion:
https://arxiv.org/pdf/2210.00388v1 . The coefficient-group convention on page 2
allows arbitrary abelian groups. For an arbitrary open cover and a natural k,
reduced intersection homology vanishing in degrees j with j+card(s) at most
k+1, for supported nonempty faces of cardinality at most k+1, gives ordinary
space-to-nerve homology isomorphisms through k and transfers nerve
nonvanishing in degree k+1 to the space. The original PDF SHA-256 is
`cb921bf0ffc4ff62ccffa13d8d83f4f48b66007cbb7180ac8625ac496f056213`.
No originality or open-problem-resolution claim is made.

The application in the owning comparison Blueprint combines that theorem's
triangular hypothesis with the actual finite-degree total comparison.
Additional attributed supply is TauCetiProject/TauCeti revision
`ff97e2dafb29b508b1229a5a7acbbca81ebcf3a1`, particularly
`TauCeti/AlgebraicTopology/Singular/Cech/OrderedQuasiIso.lean`:
https://github.com/TauCetiProject/TauCeti/blob/ff97e2dafb29b508b1229a5a7acbbca81ebcf3a1/TauCeti/AlgebraicTopology/Singular/Cech/OrderedQuasiIso.lean .
Its actual Cech total augmentation is a quasi-isomorphism for an arbitrary
open cover, using ordered free-cover contraction and small singular chains.
Coproduct homology and exact-coproduct preservation give the summand-to-column
comparison. These additional source suppliers are application inputs; they
are not retained by the total-comparison adaptation described above. They
retain the Tau Ceti contributor attribution and Apache-2.0 license.

The support-sensitive augmentation has zero target for empty intersections.
This preserves the ordinary nerve H0 convention and avoids a false
empty-space augmentation onto a nonzero coefficient group. Incidence chains
use only supported finite faces, with signed vertex deletion. Zero-row total
concentration identifies their chain complex with the support target's
total complex. Explicit endpoint and reduced-augmentation kernel transports
allow independent universes for the original space, index and coefficient
group. The resulting comparison is an isomorphism only through k and an
epimorphism at k+1. Infinite covers, empty spaces and members, and zero
coefficients remain in scope. This application introduces no new retained
mathematical declaration.

## Retirement

Replace this adaptation when the receiving project's own pinned library
provides the equivalent complete telescope and actual native total map,
and direct replacement checks discharge its mathematical consumers.

## Verified locator

https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/TotalComplex.lean

The cutoff induction and comparison endpoint are at lines 539–586:
https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/TotalComplex.lean#L539-L586
