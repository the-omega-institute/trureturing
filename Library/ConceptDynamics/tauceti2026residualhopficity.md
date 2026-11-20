---
bibkey: tauceti2026residualhopficity
authors: The Tau Ceti contributors
year: 2026
title: "Finitely generated residually finite groups are Hopfian"
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/GroupTheory/ResiduallyFinite.lean
claim: "Every surjective endomorphism of an arbitrary finitely generated residually finite group is injective."
strata_touched:
  - D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientHopficity
license: Apache-2.0
triage: anchor
---

## Verified locator

Source: https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/GroupTheory/ResiduallyFinite.lean

Immutable revision: `d91980bdc255e6e50506be147ad9bcb88eb9fcc0`.

Code artifact: `TauCeti/GroupTheory/ResiduallyFinite.lean`, theorem
`Group.ResiduallyFinite.injective_of_surjective`, by The Tau Ceti contributors
(Apache-2.0).

# Malcev Hopficity: immutable formal source

The Tau Ceti contributors' `Group.ResiduallyFinite.injective_of_surjective`
at revision `d91980bdc255e6e50506be147ad9bcb88eb9fcc0` states the theorem for
arbitrary `G : Type u` with `Group G`, `Group.FG G`, and
`Group.ResiduallyFinite G`, and arbitrary `f : G →* G`. Its premise is
`Function.Surjective f` and its conclusion is `Function.Injective f`.
This is classical Malcev Hopficity, with no novelty or open-problem claim.

The source module is `TauCeti/GroupTheory/ResiduallyFinite.lean` (57 lines,
2507 bytes; SHA-256
`836a19aa5b015d2b95b5c0f2b9fdc284ca96cea977122967841f39b3b2addcf1`).
Its only non-Mathlib prerequisite used here is
`IsMulFG.finite_monoidHom` in `TauCeti/GroupTheory/Finiteness.lean`.
That instance permits independent source and target universes and assumes
`MulOneClass M`, `IsMulFG M`, `MulOneClass N`, and `Finite N`.

## Correspondence and license

The host declaration is
`D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity.surjective_endomorphism_injective`.
Its proof preserves the supplier's finite-hom, precomposition-factorization,
and kernel argument. Packaging changes are the host namespace and theorem
name, explicit universes, and qualification of
`Group.exists_finiteIndexNormalSubgroup_notMem`. The finite-hom instance is
private in the same host namespace and is used by that proof. Its additive
generation and all unrelated donor declarations and imports are omitted.
No donor package dependency is introduced.

The donor uses Lean 4.36 and mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`; the host pins Lean 4.35 and mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The port uses the host's existing
definitions and dependency pins.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors. The complete Apache-2.0 license is
retained at `docs/reports/licenses/TauCeti-LICENSE.txt`; no additional license
copy is needed. No NOTICE chain was identified in the supplied source-tree
inquiry.

## Attestation and mathematical scope

The immutable source code attests this exact formal statement. Its module
documentation cites A. I. Malcev, *On isomorphic matrix representations of
infinite groups*, Mat. Sb. 8 (50) (1940), 405–422. The primary theorem text
of that article has not been read for this attribution; the article is not
claimed as an independently inspected attestation.

The source group is arbitrary, including infinite and noncommutative
groups. The finite objects in the argument are quotient groups and types
of homomorphisms to each fixed finite quotient. There is no finite-source,
countability, decidability, executable-inverse, fixed observation-budget,
coherent inverse-system, or complexity premise or guarantee. Free-group
applications require separately supplied residual finiteness.

## Retirement rule

When this repository's own pinned Mathlib contains an equivalent theorem
with the same universe and hypothesis scope, remove the corresponding
port and use that upstream declaration directly. Remove the private
finite-hom helper when replacing the theorem leaves it unconsumed. If the
pinned Mathlib supplies the equivalent helper first, replace that helper
by direct upstream instance use. Availability in a different revision or
an upstream merge alone does not satisfy this rule.
