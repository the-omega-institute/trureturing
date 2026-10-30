/- GID: D5/S3/Topology/TauCeti/AlgebraicTopology/Disk
   generality: G
   mirror-B: none(waiver:upstream-support-documented-in-module)
   mirror-E: none(waiver:abstract-support-without-experimental-evidence)
   anchors: []
   utility: none
   digest: TauCeti port: Dimension of universe-lifted Euclidean spaces; sphere-homology support. -/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
This file is a minimal source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/AlgebraicTopology/Disk.lean`. Only the Euclidean dimension declaration used by the
ported sphere endpoint is retained. The original Tau Ceti copyright and Apache-2.0 terms are
retained in `docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`. Retire this port only when
this repository's own pinned Mathlib provides an equivalent declaration at the full telescope and
all live consumers compile with direct replacement.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

public section

universe u

namespace TauCeti

/- The dimension of `EuclideanSpace ℝ (ULift (Fin n))`. -/
lemma finrank_euclideanSpace_ulift_fin (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (ULift.{u} (Fin n))) = n := by
  rw [finrank_euclideanSpace, Fintype.card_ulift, Fintype.card_fin]

end TauCeti
