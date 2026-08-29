/- GID: D5/S0/Computability/DescriptionComplexity/BidirectionalTransformationDescriptionBound
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/BidirectionalTransformationDescriptionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two inverse compilers bound both description costs and their distance. -/

import D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound
import Mathlib.Data.Nat.Dist

namespace D5.S0.Computability.DescriptionComplexity.BidirectionalTransformationDescriptionBound

open D5.S0.Computability.DescriptionComplexity.TransformationDescriptionBound

/-- Descriptions of transformations in both directions bound each endpoint's
complexity and hence the distance between the two endpoint complexities. -/
theorem bidirectional_transformation_description_bounds
    {Object Transformation ObjectCode TransformationCode : Type*}
    {objects : DescriptionSystem Object ObjectCode}
    {transformations : DescriptionSystem Transformation TransformationCode}
    {applies : Transformation -> Object -> Object -> Prop}
    {forwardOverhead reverseOverhead : Nat}
    (forwardCompiler : TransformationCompiler objects transformations
      objects applies forwardOverhead)
    (reverseCompiler : TransformationCompiler objects transformations
      objects applies reverseOverhead)
    {forwardTransformation reverseTransformation : Transformation}
    {x y : Object}
    (hforward : applies forwardTransformation x y)
    (hreverse : applies reverseTransformation y x) :
    descriptionComplexity objects y <=
        descriptionComplexity objects x +
          descriptionComplexity transformations forwardTransformation +
            forwardOverhead /\
      descriptionComplexity objects x <=
        descriptionComplexity objects y +
          descriptionComplexity transformations reverseTransformation +
            reverseOverhead /\
      Nat.dist (descriptionComplexity objects x) (descriptionComplexity objects y) <=
        max (descriptionComplexity transformations forwardTransformation)
            (descriptionComplexity transformations reverseTransformation) +
          max forwardOverhead reverseOverhead := by
  have forwardBound :=
    transformation_description_complexity_le forwardCompiler hforward
  have reverseBound :=
    transformation_description_complexity_le reverseCompiler hreverse
  refine ⟨forwardBound, reverseBound, ?_⟩
  rcases le_total (descriptionComplexity objects x)
      (descriptionComplexity objects y) with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy]
    have hTransformation := le_max_left
      (descriptionComplexity transformations forwardTransformation)
      (descriptionComplexity transformations reverseTransformation)
    have hOverhead := le_max_left forwardOverhead reverseOverhead
    omega
  · rw [Nat.dist_eq_sub_of_le_right hyx]
    have hTransformation := le_max_right
      (descriptionComplexity transformations forwardTransformation)
      (descriptionComplexity transformations reverseTransformation)
    have hOverhead := le_max_right forwardOverhead reverseOverhead
    omega

end D5.S0.Computability.DescriptionComplexity.BidirectionalTransformationDescriptionBound
