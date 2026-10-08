/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/SignDesign
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/SignDesign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A constant-sum sign design yields normalized densities and a sharp TV cap. -/
/-
Direct frozen dependencies: none.
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section


def designDensity {X C : Type*} [Fintype C] (c : X → C → ℝ) (R : ℝ)
    (x : X) (a : C) : ℝ := (1 + c x a) / (Fintype.card C + R)
end
end D5.S3.QuantumBounds.MerminMeasurementDependence
