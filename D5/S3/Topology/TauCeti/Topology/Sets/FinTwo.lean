/- GID: D5/S3/Topology/TauCeti/Topology/Sets/FinTwo
   generality: G
   mirror-B: none(waiver:upstream-support-documented-in-module)
   mirror-E: none(waiver:abstract-support-without-experimental-evidence)
   anchors: []
   utility: none
   digest: TauCeti port: Two-set families, unions and openness; sphere-homology support. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Topology.Defs.Basic

/-!
This file is a source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/Topology/Sets/FinTwo.lean`. Changes: import paths are namespaced under
`D5.S3.Topology.TauCeti` for this repository's pinned Mathlib. The original
Tau Ceti copyright and Apache-2.0 terms are retained in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`. Retire this port only
when this repository's own pinned Mathlib provides an equivalent declaration
at the full telescope and all live consumers compile with direct replacement.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Families of two sets

Two sets `U` and `V` give a family `![U, V]` indexed by `Fin 2`, the form in which a cover by two
sets is passed to results about covers indexed by an arbitrary type. Its union is `U ∪ V`
(`TauCeti.iUnion_vecCons`), and it is a family of open sets when `U` and `V` are open
(`TauCeti.isOpen_vecCons`).
-/

public section

namespace TauCeti

variable {X : Type*}

/-- The union of the family `![U, V]` is `U ∪ V`. -/
theorem iUnion_vecCons (U V : Set X) : ⋃ i, ![U, V] i = U ∪ V := by
  ext
  simp [Fin.exists_fin_two]

variable [TopologicalSpace X] {U V : Set X}

/-- Two open sets form a family `![U, V]` of open sets. -/
theorem isOpen_vecCons (hU : IsOpen U) (hV : IsOpen V) : ∀ i, IsOpen (![U, V] i) := by
  simp [Fin.forall_fin_two, hU, hV]

end TauCeti
