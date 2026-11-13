---
bibkey: axiommath2026acycliccarrier
authors: Lean FRO, LLC; AxiomMath contributors
year: 2026
title: Carried homotopies in TernaryPoly and the ordinary basis-local acyclic carrier theorem
doi: null
url: https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532
claim: The immutable source supplies the rational equivariant carried-homotopy induction; the receiving theorem extends its carrier interface to ordinary bases over arbitrary commutative rings.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Basis-local acyclic carrier homotopies

The classical ancestor is James R. Munkres, *Elements of Algebraic
Topology*, §13, Theorem 13.4, the acyclic carrier theorem for augmented
simplicial chain complexes. This identifies the classical construction;
it is not an attestation that Munkres states the exact arbitrary-ring,
ordinary-module-basis telescope used here.

## Immutable source correspondence

The source is `AxiomMath/TernaryPoly` at
`28679d7cad438a91a732422d4ab1b184ae17e532`, specifically
`BoundaryComparison/FacePairingFull/CapCompat/Carriers.lean` and
`BoundaryComparison/FacePairingFull/CapCompat/Cells.lean`.
Its `CarrierData.exists_carried_homotopy` supplies a rational equivariant
component induction. The receiving
`D5/S3/HomologicalAlgebra/AcyclicCarrier.lean` retains that mechanism,
including the dependent primitive sequence and residual-cycle invariant.
The receiving interface uses ordinary `Module.Basis` families over an
arbitrary `CommRing`, with independent scalar, module-object and
basis-index universes. Source and target complexes inhabit one common
`ModuleCat` category, as required for native maps and `Homotopy`.

The interface extension chooses carrier primitives on basis vectors and
extends them by `Basis.constr`. Expanding a source boundary by
`Basis.repr` uses only its finite coefficient support; coefficient-support
nesting puts every summand in the required carrier. These steps remove
the source's rational equivariant cell-basis restriction. The final
ordinary theorem specializes the signed induction to sign one and
constructs a native homotopy with all original basis-local bounds.
It allows zero rings, empty or infinite basis index types, and
non-surjective augmentations. It assumes neither target projectivity,
a target basis, global acyclicity nor a chosen homotopy or contraction.
This is an interface generalization of known mathematics, with no
originality or external open-problem resolution claim.

The source pins Lean `v4.35.0-rc3` and Mathlib revision beginning `c55e`;
the receiving repository pins Lean `v4.35.0` and Mathlib revision
beginning `56a`. This is a source port, not a claim of binary or package
compatibility across these pins. Replace the port by direct library use
only when the receiving repository's current pinned Mathlib supplies an
equivalent full theorem including all basis-local carrier bounds.
Acceptance in another upstream revision alone is insufficient; there is
no upstream-acceptance deadline.

## Copyright and license

The original attribution is **Formalized by Claude Sonnet 5.5**.
The complete Apache License, Version 2.0, including the actual
`Copyright 2026 Lean FRO, LLC`, is retained verbatim in the receiving
Lean source, together with its modification and source notices.
The immutable complete source tree has no `NOTICE` file.
The Scribe mathematical exposition is repository-authored and acknowledges
this source; its acknowledgement does not attest that the source already
contains the receiving arbitrary-ring theorem.

## Verified locator

https://github.com/AxiomMath/TernaryPoly/tree/28679d7cad438a91a732422d4ab1b184ae17e532
