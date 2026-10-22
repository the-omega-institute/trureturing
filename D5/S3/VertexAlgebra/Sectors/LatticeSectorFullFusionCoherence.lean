/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFullFusionCoherence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFullFusionCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identity and composition coherence for actual full IO target postcomposition. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFullFusion

/-!
The actual target-map action on the complete mixed-target IO subspace is
functorial for the explicit finite-sector category.  The existing pointwise
coefficient formula is lifted to identity and composition coherence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators
noncomputable section
namespace FiniteSectorObject
variable (D : LatticeData)

/-- Postcomposition by the identity module map is the identity on full IO. -/
theorem fullPost_identity (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (M : FiniteSectorObject D) (I : FullIO D α β M) :
    fullPost D H hHG hGH α β (identity D M) I = I := by
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  funext n
  apply LinearMap.ext
  intro v
  rw [fullPost_apply]
  rfl

/-- Full target postcomposition respects composition of actual module maps. -/
theorem fullPost_comp (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) {M N P : FiniteSectorObject D}
    (g : Hom D M N) (h : Hom D N P) (I : FullIO D α β M) :
    fullPost D H hHG hGH α β (compose D h g) I =
      fullPost D H hHG hGH α β h (fullPost D H hHG hGH α β g I) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  funext n
  apply LinearMap.ext
  intro v
  rw [fullPost_apply, fullPost_apply, fullPost_apply]
  rfl

end FiniteSectorObject
end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
