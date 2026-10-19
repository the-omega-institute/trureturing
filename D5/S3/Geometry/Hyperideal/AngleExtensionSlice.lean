/- GID: D5/S3/Geometry/Hyperideal/AngleExtensionSlice
   generality: I
   mirror-B: D5/B/S3/Geometry/Hyperideal/AngleExtensionSlice
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/Hyperideal/AngleExtensionSlice.claim; result=D5/S3/Geometry/Hyperideal/AngleExtensionSlice.result; claim=D5/S3/Geometry/Hyperideal/AngleExtensionSlice.claim
   digest: The first-slot cosine on the Section 68 scalar slice is not constant at its endpoint. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Tactic

/-!
The first-slot hyper-ideal cosine on the Section 68 scalar slice

  (2, 2, 2, 17 - ε, 2, 2)

equals `-1 + ε / 9`.  The certified refutation below records the
nonconstancy already at `ε = 1 / 2`; it does not assert the full
inverse-cosine regularity statement or a global flow consequence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.AngleExtensionSlice

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-- The first-slot cosine along the scalar length slice from Section 68. -/
def endpointSlice (ε : ℝ) : ℝ := cosine 2 2 2 (17 - ε) 2 2

/-- The endpoint value would be constant along this slice if the claim held. -/
def claim : Prop := ∀ ε : ℝ, ε ∈ Set.Icc 0 1 → endpointSlice ε = -1

/-- The scalar slice leaves the endpoint value at the explicit parameter `1/2`. -/
theorem result : ¬ claim := by
  intro h
  have hslice := h (1 / 2 : ℝ) (by constructor <;> norm_num)
  unfold endpointSlice cosine numerator rad at hslice
  have hs : (Real.sqrt (27 : ℝ)) ^ 2 = 27 :=
    Real.sq_sqrt (by norm_num)
  have hden : Real.sqrt (27 : ℝ) * Real.sqrt (27 : ℝ) = 27 := by
    nlinarith [hs]
  norm_num [hden] at hslice
  field_simp at hslice
  nlinarith [hs]

#print axioms result

end D5.S3.Geometry.Hyperideal.AngleExtensionSlice
