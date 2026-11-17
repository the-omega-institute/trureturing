---
bibkey: tauceti2026vankampenneighborhoodcover
authors: The Tau Ceti contributors; Kim Morrison; Lean FRO, LLC
year: 2026
title: Fundamental-groupoid gluing for arbitrary neighborhood covers
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean
claim: Compatible functors on an arbitrary neighborhood cover glue uniquely to the full topological fundamental groupoid, and the ordinary finite-intersection open-cover Cech cocone is a colimit in groupoids.
strata_touched:
  - D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover
license: Apache-2.0
triage: anchor
---

# Fundamental-groupoid gluing for arbitrary neighborhood covers

The received source is attributed to the Tau Ceti contributors, Kim Morrison,
and Lean FRO, LLC. The immutable source Git commit is
`3780371ca1bebf9f1c2bb3d753e4bb56c9526023`. The retained source spans include the
gluing construction, lines 63–689 and 699–701, at the immutable
[`Glue.lean`](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean),
SHA-256
`a2ba1b2fb84296ee7bff70ff525d7c3c057aa7d85af1eb39a4c7965938b80377`, and the
ordinary Cech construction, lines 55–152, at the immutable
[`Cech/Colimit.lean`](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Cech/Colimit.lean),
SHA-256
`73a0bbcd052c6988eac1fedc40cc3b1d0b124d9d16aed8bed17859e1b78a4d21`.

The owner also directly receives the following definitions and helper proofs.
These are literature sources, including the copied diagram and cocone data;
they are not locally derived definitions. Line spans refer to the immutable
supplier files, and each SHA-256 identifies the complete file bytes.

| Immutable supplier source | Directly received spans and declarations | SHA-256 |
| --- | --- | --- |
| [FundamentalGroupoid/Cech/Diagram.lean](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Cech/Diagram.lean#L44-L98) | Lines 44–45: `cechDiagram`; 48–63: object/map helpers; 66–68: `cechCocone`; 71–98: cocone helpers. The two definition bodies agree after whitespace normalization. | `f3f7ecad8737c028e7aed332f4879d64d9a2131cef78b95d0c6ca74d6bba85ec` |
| [TopCat/Cech/Diagram.lean](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/Topology/Category/TopCat/Cech/Diagram.lean#L40-L143) | Lines 40–85 and 99–143: `CechIndex`, singleton/order helpers, `cechIntersection` and its helpers, `cechOpenDiagram`, `cechTopDiagram`, inclusions and the natural transformation, and singleton coverage. Unused supplier wrappers at 88–96 are omitted; the inclusion-composition lemma retains only its `simp` attribute. | `cba6a575c843daeefb77f026754e33f4f40b436e6559a541e3099407dd07a41c` |
| [FundamentalGroupoid/CoverGeneration.lean](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/CoverGeneration.lean#L64-L168) | Lines 64–168: `mk_mem_iSup_im`, `mk_concat_mem_iSup_im`, `iSup_im_map_subtypeVal_eq_top`, and `functor_ext`. | `1df069a0545216aca8e7decaf1bf15065db34a29429d7241eb642eeee2d4b1fa` |
| [FundamentalGroupoid/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Basic.lean#L50-L84) | Lines 50–60: `cast_mem_arrows_iff`; 80–84: `fundamentalGroupoid_map_obj_injective`. | `85c649143c6023fcd344c82c9e8d0d7d2516b8f0f87014341e9e83640187bcc1` |
| [MetricSpace/Lebesgue.lean](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/Topology/MetricSpace/Lebesgue.lean#L39-L45) | Lines 39–45: `lebesgue_number_lemma_of_metric_of_mem_nhds`. | `b8275adb018c482de7f94badc13a399e51d6cef918dd502603525fc8674bf290` |

The receiver makes helper declarations private and adapts proofs to its pinned
APIs. `existsUnique_extension` packages the received gluing construction,
restriction law and uniqueness result into the full strict `ExistsUnique`
statement. The private `cechExtension` applies that theorem to the singleton
legs; `isColimitCechCocone` consumes this application as colimit data.

The source pin is Lean 4.36.0-rc2 with Mathlib
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`; the receiving project uses Lean
4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The source
was adapted to the receiving Path and UnitInterval APIs and native
fundamental-groupoid interfaces. The retained theorem keeps arbitrary spaces,
index types, target categories, neighborhood members that need not be open,
empty intersections, strict restriction equalities, and the full
existence-and-uniqueness conclusion. The Cech diagram uses nonempty finite
subsets ordered by reverse inclusion and retains geometrically empty
intersections as objects; its universal property is an ordinary `IsColimit` in
`Grpd`.

The fixed private path invariant is `lift_eq_of_homotopy`; it identifies the
lift of homotopic paths and is used on the live quotient-map path in the
internal glue construction. No natural-isomorphism or pseudocolimit statement is part
of this source.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved. Authors:
The Tau Ceti contributors; Kim Morrison; Lean FRO, LLC. The full Apache-2.0
license is retained in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.

No novelty, priority, or first-formalization claim is made. The verified
locators are the immutable Tau Ceti Git commit and the source blobs linked above.

## Retirement

Replace this adaptation when the receiving project, at its adopted Lean and
Mathlib pin, supplies a native replacement with the same complete strict
arbitrary-neighborhood-cover telescope, live homotopy invariant, and ordinary
Cech colimit consumer, and direct scoped checks at that adopted pin discharge
both replacement declarations.

## Verified locator

https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean
