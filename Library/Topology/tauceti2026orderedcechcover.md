---
bibkey: tauceti2026orderedcechcover
authors: The Tau Ceti contributors
year: 2026
title: Ordered free Cech complexes of set covers
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/OrderedCech/Cover.lean
claim: The actual augmentation of an ordered free set-cover complex has an explicit chosen-vertex chain contraction in an arbitrary preadditive category with coproducts and a zero object.
strata_touched:
  - D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover
license: Apache-2.0
triage: anchor
---

# Ordered free complexes of set covers

The immutable source is TauCetiProject/TauCeti revision
`580580ea8726c50dcf98e199fa0a7caef5a74302`. The selected source files are
`TauCeti/Algebra/Homology/OrderedCech.lean` (338 lines, SHA-256
`9948f62d2aa28e8e9d3f1be21e97233747d4b2a47059f606d288f999fc4379ba`),
`TauCeti/Algebra/Homology/OrderedCech/Cover.lean` (381 lines, SHA-256
`4a469069de47b98bf2439b22d1570b79031a4210e57b222c38b8776004f06a62`),
and the insertion-sign and erasure-sign span at lines 441–473 of
`TauCeti/Data/Finset/Basic.lean` (33 lines, SHA-256
`8d6d7c246b1ca4786f0255cb38e363345ee755623416af9508a4f615fe4c84d2`).
Only the insertion-sign identity of that span is retained.

The source pins Lean 4.36.0-rc1 and Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`. The receiving project pins
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The unequal pins require a focused source adaptation rather than a new dependency.
The free intersection functor, actual ordered complex and augmentation, pointwise
chosen covering vertex, signed insertion, section and contraction are retained.
The generic functorial hierarchy, natural-transformation API, colimit companions
and forward-map reflexivity companion are excluded. Coproduct and single-complex
interfaces use the receiving Mathlib. Increasing finite-set enumeration transports
the actual double deletion to the existing local TauCeti alternating-sum theorem;
the source's separate pair-involution proof is excluded.

The source theorem `TauCeti.freeCechHomotopyEquiv` has independent object,
morphism and index universes, arbitrary preadditive coefficients, all natural
degrees, and no finiteness or nonemptiness condition. Its sole additional
set-theoretic hypothesis is that the family covers its point type. These
conditions are retained. The receiving endpoint states existence of a
homotopy equivalence with forward map equal to the independently defined
augmentation. It does not assume square-zero or a supplied contraction.
The native null-homotopic-map assembler is applied only after the actual
cone identities are proved on all summands.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors. The full Apache-2.0 license is already
retained in [the Tau Ceti license](../../docs/reports/licenses/tauceti-sphere-port-LICENSE.txt),
201 lines and 11357 bytes, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
It is byte-for-byte the license at the selected source revision. The complete
immutable Git tree has no NOTICE file. The original attribution and the
modification notice are retained in the receiving Lean source.

The Bott–Tu §8 citation in the source is a bibliographic pointer. The exact
arbitrary-category print text has not been read, and no original-paper reading,
priority or mathematical originality claim is made here. The verified source
for this adaptation is the pinned Lean text.

## Retirement

Replace this adaptation when the receiving project's own pinned libraries supply
the complete telescope and the same actual augmentation, and direct replacement
checks discharge all its mathematical consumers.

## Verified locator

https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/OrderedCech/Cover.lean

The selected declarations are the intersection functor and point inclusions,
`TauCeti.FreeCech.vertex`, the signed homotopy and cone-face identities,
the section, `id_sub_freeCechAugmentation_comp_section`, and
`TauCeti.freeCechHomotopyEquiv`. The actual ordered differential and complex are in
https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Algebra/Homology/OrderedCech.lean
The finite-set insertion-sign identity is in
https://github.com/TauCetiProject/TauCeti/blob/580580ea8726c50dcf98e199fa0a7caef5a74302/TauCeti/Data/Finset/Basic.lean#L441-L456
