/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFullChannelNaturality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFullChannelNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: FullIO channel transport is natural for actual finite-target module maps. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
import Batteries.Tactic.OpenPrivate

/-!
The channel equivalence is defined from the actual incoming universal maps.
This module proves that it is natural in the finite target: postcomposing a
lawful FullIO field before or after the channel gives the same actual field.
The result is the target-morphism edge needed when the finite channel maps are
assembled into a coherent fusion system; it uses the existing classification
and does not introduce an analytic sewing or a formal associator axiom.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorFullChannelNaturality

open LatticeSectorIntertwiner
open LatticeSectorIntertwiner.FiniteSectorObject
open LatticeSectorChannelTransport
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open scoped BigOperators
noncomputable section

open private incomingAssoc from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport

private theorem incomingAssoc_natural (D : LatticeData)
    {α β γ : Charge D} {M N : FiniteSectorObject D}
    (g : Hom D M N) (f : Incoming D (α + (β + γ)) M) :
    incomingPost D ((α + β) + γ) g
        (incomingAssoc D α β γ M f) =
      incomingAssoc D α β γ N
        (incomingPost D (α + (β + γ)) g f) := by
  apply Subtype.ext
  rfl

/-- The actual FullIO channel commutes with every finite-target module map. -/
theorem fullChannel_natural
    (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ : Charge D) {M N : FiniteSectorObject D}
    (g : Hom D M N) :
    (fullPost D H hHG hGH (α + β) γ g).comp
        (fullChannel D H hHG hGH α β γ M).toLinearMap =
      (fullChannel D H hHG hGH α β γ N).toLinearMap.comp
        (fullPost D H hHG hGH α (β + γ) g) := by
  apply LinearMap.ext
  intro F
  let f := (fullUniversal D H hHG hGH α (β + γ) M).symm F
  have rightUniversal :
      (fullUniversal D H hHG hGH α (β + γ) N).symm
        (fullPost D H hHG hGH α (β + γ) g F) =
        incomingPost D (α + (β + γ)) g f := by
    apply (fullUniversal D H hHG hGH α (β + γ) N).injective
    rw [LinearEquiv.apply_symm_apply]
    rw [← (fullUniversal D H hHG hGH α (β + γ) M).apply_symm_apply F]
    exact (fullUniversal_natural D H hHG hGH α (β + γ) g f).symm
  change
    fullPost D H hHG hGH (α + β) γ g
        (fullChannel D H hHG hGH α β γ M F) =
      fullChannel D H hHG hGH α β γ N
        (fullPost D H hHG hGH α (β + γ) g F)
  simp only [fullChannel, LinearEquiv.trans_apply]
  rw [rightUniversal]
  rw [← fullUniversal_natural D H hHG hGH (α + β) γ g
      (incomingAssoc D α β γ M f)]
  rw [incomingAssoc_natural D g f]

#print axioms fullChannel_natural

end
end D5.S3.VertexAlgebra.LatticeSectorFullChannelNaturality
