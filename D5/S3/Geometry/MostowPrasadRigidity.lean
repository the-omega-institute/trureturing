/- GID: D5/S3/Geometry/MostowPrasadRigidity
   generality: G
   mirror-B: D5/B/S3/Geometry/MostowPrasadRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Isometry]
   utility: none
   digest: An isometry equivalence is uniquely determined by its values on a dense subset.
 -/

import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.MostowPrasadRigidity

/-!
This is the metric uniqueness interface needed by the Mostow--Prasad endpoint.
It does not encode hyperbolic curvature, finite volume, or the existence part of
Mostow--Prasad rigidity. Those geometric inputs remain separate obligations.
-/

/-- Two isometric bijections with the same values on a dense subset are equal. -/
theorem isometry_equiv_eq_of_eqOn_dense
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (s : Set X) (hs : Dense s) (f g : X ≃ᵢ Y)
    (hfg : Set.EqOn f g s) :
    f = g := by
  apply IsometryEquiv.ext
  have hfun : (f : X → Y) = g :=
    hs.denseRange_val.equalizer f.continuous g.continuous (by
      funext x
      exact hfg x.2)
  exact fun x => congrFun hfun x

/- A pointwise form is convenient when the dense set is supplied by a subtype. -/
theorem isometry_equiv_eq_of_dense_range
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
    [MetricSpace Z] (e : Z → X) (he : DenseRange e)
    (f g : X ≃ᵢ Y) (hfg : f ∘ e = g ∘ e) :
    f = g := by
  apply IsometryEquiv.ext
  have hfun : (f : X → Y) = g :=
    he.equalizer f.continuous g.continuous hfg
  exact fun x => congrFun hfun x

#print axioms isometry_equiv_eq_of_eqOn_dense
#print axioms isometry_equiv_eq_of_dense_range

end D5.S3.Geometry.MostowPrasadRigidity
