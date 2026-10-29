import Mathlib.Analysis.Normed.Group.BallSphere

/-!
This file is a source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/Analysis/Normed/Group/BallSphere.lean`. Changes: the source is
namespaced under `D5.S3.Topology.TauCeti` by the receiving import path. The original Tau Ceti
copyright and Apache-2.0 terms are retained in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`. Retire this port only when this
repository's own pinned Mathlib provides an equivalent declaration at the full telescope and all
live consumers compile with direct replacement.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

public section

open Metric

namespace TauCeti

/- The complements of two antipodal points cover a nonzero-radius sphere. -/
lemma compl_singleton_union_compl_singleton_neg {E : Type*} [SeminormedAddCommGroup E]
    [IsAddTorsionFree E] {r : ℝ} (hr : r ≠ 0) (p : sphere (0 : E) r) :
    ({p}ᶜ ∪ {-p}ᶜ : Set (sphere (0 : E) r)) = Set.univ := by
  rw [← Set.compl_inter, Set.singleton_inter_of_notMem]
  · exact Set.compl_empty
  · intro h
    apply ne_zero_of_mem_sphere hr p
    apply self_eq_neg.mp
    simpa only [coe_neg_sphere] using congrArg Subtype.val h

end TauCeti
