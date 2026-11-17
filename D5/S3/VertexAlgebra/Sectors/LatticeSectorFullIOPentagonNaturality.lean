/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagonNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite-target FullIO pentagon paths are natural in the target module. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFullIOPentagon
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFullChannelNaturality

/-!
The explicit five-vertex FullIO paths commute with postcomposition by every
finite-target module morphism.  The short-path result is obtained by composing
the two already-proved channel naturality squares.  The long-path result is
then transported across the concrete finite-target pentagon at both endpoints.
-/

set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorFullIOPentagonNaturality

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeSectorIntertwiner
open LatticeSectorIntertwiner.FiniteSectorObject
open LatticeSectorChannelTransport
open D5.S3.VertexAlgebra.LatticeSectorFullIOPentagon
open D5.S3.VertexAlgebra.LatticeSectorFullChannelNaturality
open scoped BigOperators
noncomputable section

/-- The short side `A → C → E` is natural in the finite target. -/
theorem pentagonShortPath_natural
    (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) {M N : FiniteSectorObject D}
    (g : Hom D M N) :
    (fullPost D H hHG hGH ((α + β) + γ) δ g).comp
        (pentagonShortPath D H hHG hGH α β γ δ M).toLinearMap =
      (pentagonShortPath D H hHG hGH α β γ δ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + (γ + δ)) g) := by
  apply LinearMap.ext
  intro F
  change fullPost D H hHG hGH ((α + β) + γ) δ g
      (pentagonShortPath D H hHG hGH α β γ δ M F) =
    pentagonShortPath D H hHG hGH α β γ δ N
      (fullPost D H hHG hGH α (β + (γ + δ)) g F)
  simp only [pentagonShortPath, LinearEquiv.trans_apply]
  change (fullPost D H hHG hGH ((α + β) + γ) δ g)
      ((fullChannel D H hHG hGH (α + β) γ δ M).toLinearMap
        ((fullChannel D H hHG hGH α β (γ + δ) M).toLinearMap F)) =
    (fullChannel D H hHG hGH (α + β) γ δ N).toLinearMap
      ((fullChannel D H hHG hGH α β (γ + δ) N).toLinearMap
        ((fullPost D H hHG hGH α (β + (γ + δ)) g) F))
  have h₂ := fullChannel_natural D H hHG hGH (α + β) γ δ g
  have h₁ := fullChannel_natural D H hHG hGH α β (γ + δ) g
  have e₂ := congrArg
    (fun k => k ((fullChannel D H hHG hGH α β (γ + δ) M).toLinearMap F)) h₂
  have e₁ := congrArg (fun k => k F) h₁
  simpa only [LinearMap.comp_apply] using e₂.trans (congrArg
    (fun x => (fullChannel D H hHG hGH (α + β) γ δ N).toLinearMap x) e₁)

/-- The long side `A → B → D → E` is natural in the finite target. -/
theorem pentagonLongPath_natural
    (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) {M N : FiniteSectorObject D}
    (g : Hom D M N) :
    (fullPost D H hHG hGH ((α + β) + γ) δ g).comp
        (pentagonLongPath D H hHG hGH α β γ δ M).toLinearMap =
      (pentagonLongPath D H hHG hGH α β γ δ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + (γ + δ)) g) := by
  calc
    (fullPost D H hHG hGH ((α + β) + γ) δ g).comp
        (pentagonLongPath D H hHG hGH α β γ δ M).toLinearMap =
      (fullPost D H hHG hGH ((α + β) + γ) δ g).comp
        (pentagonShortPath D H hHG hGH α β γ δ M).toLinearMap := by
      rw [fullIO_pentagon D H hHG hGH α β γ δ M]
    _ = (pentagonShortPath D H hHG hGH α β γ δ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + (γ + δ)) g) :=
      pentagonShortPath_natural D H hHG hGH α β γ δ g
    _ = (pentagonLongPath D H hHG hGH α β γ δ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + (γ + δ)) g) := by
      rw [fullIO_pentagon D H hHG hGH α β γ δ N]

/-- The concrete finite-target pentagon equality is natural in the target. -/
theorem fullIO_pentagon_natural
    (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) {M N : FiniteSectorObject D}
    (g : Hom D M N) :
    (fullPost D H hHG hGH ((α + β) + γ) δ g).comp
        (pentagonShortPath D H hHG hGH α β γ δ M).toLinearMap =
      (pentagonLongPath D H hHG hGH α β γ δ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + (γ + δ)) g) := by
  calc
    (fullPost D H hHG hGH ((α + β) + γ) δ g).comp
        (pentagonShortPath D H hHG hGH α β γ δ M).toLinearMap =
      (fullPost D H hHG hGH ((α + β) + γ) δ g).comp
        (pentagonShortPath D H hHG hGH α β γ δ M).toLinearMap := rfl
    _ = (pentagonShortPath D H hHG hGH α β γ δ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + (γ + δ)) g) :=
      pentagonShortPath_natural D H hHG hGH α β γ δ g
    _ = (pentagonLongPath D H hHG hGH α β γ δ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + (γ + δ)) g) := by
      rw [fullIO_pentagon D H hHG hGH α β γ δ N]

#print axioms pentagonShortPath_natural
#print axioms pentagonLongPath_natural
#print axioms fullIO_pentagon_natural

end
end D5.S3.VertexAlgebra.LatticeSectorFullIOPentagonNaturality
