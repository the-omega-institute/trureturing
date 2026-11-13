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
`3780371ca1bebf9f1c2bb3d753e4bb56c9526023`. The retained source spans are the
gluing construction at the immutable
[`Glue.lean`](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean),
SHA-256
`a2ba1b2fb84296ee7bff70ff525d7c3c057aa7d85af1eb39a4c7965938b80377`, and the
ordinary Cech construction at the immutable
[`Cech/Colimit.lean`](https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Cech/Colimit.lean),
SHA-256
`73a0bbcd052c6988eac1fedc40cc3b1d0b124d9d16aed8bed17859e1b78a4d21`.

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
locator is the immutable Tau Ceti Git commit and its `Glue.lean` and
`Cech/Colimit.lean` blobs linked above.

## Retirement

Replace this adaptation when the receiving project, at its adopted Lean and
Mathlib pin, supplies a native replacement with the same complete strict
arbitrary-neighborhood-cover telescope, live homotopy invariant, and ordinary
Cech colimit consumer, and direct scoped checks at that adopted pin discharge
both replacement declarations.

## Verified locator

https://github.com/TauCetiProject/TauCeti/blob/3780371ca1bebf9f1c2bb3d753e4bb56c9526023/TauCeti/AlgebraicTopology/FundamentalGroupoid/Glue.lean
