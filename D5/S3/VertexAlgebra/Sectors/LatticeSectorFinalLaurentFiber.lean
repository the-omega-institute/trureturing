/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual canonical and Jacobi consumers of the finite final Laurent fiber. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorMiddleCommonNumerator
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentFiber

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorFinalLaurentFiber
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorThreeFieldInnerIterate
open LatticeSectorSecondCollisionSlice LatticeSectorMiddleCommonNumerator
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open SupportedChannelSeries SupportedThreeFieldCollision SupportedMiddleCollision
open SupportedCollisionSlice ThreeFieldFinalLaurentFiber
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

/-- The actual fully left-nested channel requested in the task. This is K,
with the original modes -x-1,-y-1,-z-1 and the original charge additions. -/
def leftNested (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ)
    (x y z : ℤ) : Oscillator D :=
  canonical D ((α + β) + γ) δ
    (canonical D (α + β) γ (canonical D α β u (-x - 1) v) (-y - 1) t)
    (-z - 1) w

end
end D5.S3.VertexAlgebra.LatticeSectorFinalLaurentFiber
