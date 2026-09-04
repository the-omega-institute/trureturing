/- GID: D5/S0/Computability/DescriptionComplexity/AlmostEverywhereTransformationDescriptionBound
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/AlmostEverywhereTransformationDescriptionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Eventual reverse transformation costs lift to an a.e. description bound, not a pointwise one. -/

import D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory

namespace D5.S0.Computability.DescriptionComplexity.AlmostEverywhereTransformationDescriptionBound

open D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound

/-- If a reverse transformation is eventually applicable and its description
cost plus compiler overhead is eventually bounded, then the reverse endpoint
description bound holds eventually for almost every sample. -/
theorem almost_everywhere_reverse_description_bound
    {Sample Object Transformation ObjectCode TransformationCode : Type*}
    [MeasurableSpace Sample]
    {objects : DescriptionSystem Object ObjectCode}
    {transformations : DescriptionSystem Transformation TransformationCode}
    {applies : Transformation -> Object -> Object -> Prop}
    {reverseOverhead : Nat}
    (mu : Measure Sample)
    (reverseCompiler : TransformationCompiler objects transformations
      objects applies reverseOverhead)
    (sourceObject transformedObject : Sample -> Nat -> Object)
    (reverseTransformation : Sample -> Nat -> Transformation)
    (bound : Nat -> Nat)
    (happly : ∀ᵐ sample ∂mu, ∀ᶠ Q in atTop,
      applies (reverseTransformation sample Q)
        (transformedObject sample Q) (sourceObject sample Q))
    (hcost : ∀ᵐ sample ∂mu, ∀ᶠ Q in atTop,
      descriptionComplexity transformations (reverseTransformation sample Q) +
        reverseOverhead <= bound Q) :
    ∀ᵐ sample ∂mu, ∀ᶠ Q in atTop,
      descriptionComplexity objects (sourceObject sample Q) <=
        descriptionComplexity objects (transformedObject sample Q) + bound Q := by
  filter_upwards [happly, hcost] with sample hApply hCost
  filter_upwards [hApply, hCost] with Q hApplyAtQ hCostAtQ
  have hCompiled :=
    transformation_description_complexity_le reverseCompiler hApplyAtQ
  omega

#print axioms almost_everywhere_reverse_description_bound

/-- An a.e. family of natural-number bounds need not hold pointwise. For every
proposed bound, the displayed cost exceeds it at the origin and vanishes away
from that Lebesgue-null point. -/
theorem almost_everywhere_bound_does_not_imply_pointwise
    (g : Nat -> Nat) :
    exists cost : Real -> Nat -> Nat,
      (∀ᵐ x ∂(volume : Measure Real), forall Q, cost x Q <= g Q) /\
      (forall Q, not (cost 0 Q <= g Q)) := by
  refine ⟨fun x Q => if x = 0 then g Q + 1 else 0, ?_, ?_⟩
  · filter_upwards [(volume : Measure Real).ae_ne 0] with x hx
    intro Q
    simp [hx]
  · intro Q
    simp

#print axioms almost_everywhere_bound_does_not_imply_pointwise

end D5.S0.Computability.DescriptionComplexity.AlmostEverywhereTransformationDescriptionBound
