/- GID: D5/S3/QuadraticForms/ConicGDNN/Result
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ConicGDNN/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The generalized doubly nonnegative cone inclusion on orthant and Lorentz products. -/

import D5.S3.QuadraticForms.ConicGDNN.Duality

namespace D5.S3.QuadraticForms.ConicGDNN.Result
open Defs Duality

/-- The dual sum of squares approximation is contained in the extreme ray preserving cone. -/
theorem result : claim := by
  intro p r k _hk Xm hXm
  refine ⟨posSemidef_of_mem_dnnNN hXm, ?_⟩
  intro s hs
  apply mulVec_mem_cone hXm
  rw [← Lorentz.dualCone_cone p r k]
  exact hs.1

end D5.S3.QuadraticForms.ConicGDNN.Result
