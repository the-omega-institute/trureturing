/- GID: D5/S3/Topology/TauCeti/Analysis/Normed/Module/Normalize
   generality: G
   mirror-B: none(waiver:upstream-support-documented-in-module)
   mirror-E: none(waiver:abstract-support-without-experimental-evidence)
   anchors: []
   utility: none
   digest: TauCeti port: Continuous radial projection to the unit sphere; sphere support. -/

import Mathlib.Analysis.Normed.Module.Normalize

/-!
This file is a source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/Analysis/Normed/Module/Normalize.lean`. Changes: import paths are namespaced under
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
# Radial projection to the unit sphere

This file packages pointwise normalization of a continuous nowhere-zero map as a continuous map
to the unit sphere.
-/

public section

noncomputable section

open Metric NormedSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection sends a continuous nowhere-zero map into a real normed space continuously
to its unit sphere. -/
noncomputable def normalizeToSphere {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) : C(Y, sphere (0 : E) 1) where
  toFun y := ⟨normalize (f y), mem_sphere_zero_iff_norm.mpr (norm_normalize (h0 y))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [NormedSpace.normalize]
    exact ((continuous_norm.comp hf).inv₀
      (fun y => norm_ne_zero_iff.mpr (h0 y))).smul hf

/-- The underlying vector of `normalizeToSphere f hf h0 y` is the normalization of `f y`. -/
@[simp]
theorem coe_normalizeToSphere_apply {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) (y : Y) :
    ((normalizeToSphere f hf h0 y : sphere (0 : E) 1) : E) = normalize (f y) :=
  (rfl)

end TauCeti

end
