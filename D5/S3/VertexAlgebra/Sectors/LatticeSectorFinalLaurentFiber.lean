/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual left-nested canonical three-field channel. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport

set_option autoImplicit false
namespace D5.S3.VertexAlgebra.LatticeSectorFinalLaurentFiber
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSectorIntertwiner
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
