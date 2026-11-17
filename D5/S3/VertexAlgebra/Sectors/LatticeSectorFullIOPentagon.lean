/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagon
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFullIOPentagon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite-target FullIO associator satisfies the explicit five-vertex pentagon. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldFullIOReadout

/-!
The five vertices of the associativity pentagon are exposed explicitly:

```
 A = α + (β + (γ + δ))
 B = α + ((β + γ) + δ)
 C = (α + β) + (γ + δ)
 D = (α + (β + γ)) + δ
 E = ((α + β) + γ) + δ.
```

Every edge below is the concrete linear equivalence induced by the existing
universal incoming maps.  The theorem is the finite FullIO pentagon for these
maps; it introduces no analytic sewing or abstract associator axiom.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorFullIOPentagon

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeSectorIntertwiner
open LatticeSectorIntertwiner.FiniteSectorObject
open LatticeSectorChannelTransport
open scoped BigOperators
noncomputable section

private def incomingChargeAssoc (D : LatticeData) {p q : Charge D}
    (M : FiniteSectorObject D) (h : p = q) :
    Incoming D p M ≃ₗ[ℂ] Incoming D q M where
  toFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) h
    exact (congrArg f.val e).symm.trans (f.property a n x)⟩
  invFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) h
    exact (congrArg f.val e).trans (f.property a n x)⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' f g := rfl
  map_smul' c f := rfl

private def middleAssoc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + (γ + δ)) M ≃ₗ[ℂ] FullIO D α ((β + γ) + δ) M :=
  (fullUniversal D H hHG hGH α (β + (γ + δ)) M).symm.trans
    ((incomingChargeAssoc D M (by rw [add_assoc β γ δ])).trans
      (fullUniversal D H hHG hGH α ((β + γ) + δ) M))

private def inputAssoc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    {p q β : Charge D} (M : FiniteSectorObject D) (h : p = q) :
    FullIO D p β M ≃ₗ[ℂ] FullIO D q β M :=
  (fullUniversal D H hHG hGH p β M).symm.trans
    ((incomingChargeAssoc D M (by simpa [h])).trans
      (fullUniversal D H hHG hGH q β M))

/-- The short side of the five-vertex pentagon, `A → C → E`. -/
def pentagonShortPath (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + (γ + δ)) M ≃ₗ[ℂ] FullIO D ((α + β) + γ) δ M :=
  (fullChannel D H hHG hGH α β (γ + δ) M).trans
    (fullChannel D H hHG hGH (α + β) γ δ M)

/-- The long side of the five-vertex pentagon, `A → B → D → E`. -/
def pentagonLongPath (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + (γ + δ)) M ≃ₗ[ℂ] FullIO D ((α + β) + γ) δ M :=
  (middleAssoc D H hHG hGH α β γ δ M).trans
    ((fullChannel D H hHG hGH α (β + γ) δ M).trans
      (inputAssoc D H hHG hGH M (add_assoc α β γ).symm))

/--
The actual finite-target pentagon.  The proof compares both composites after
the common universal incoming equivalence, so the equality is about the
concrete FullIO maps rather than a postulated associator.
-/
theorem fullIO_pentagon (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    pentagonShortPath D H hHG hGH α β γ δ M =
      pentagonLongPath D H hHG hGH α β γ δ M := by
  apply LinearEquiv.ext
  intro F
  apply (fullUniversal D H hHG hGH ((α + β) + γ) δ M).symm.injective
  simp only [pentagonShortPath, pentagonLongPath, LinearEquiv.trans_apply]
  simp [add_assoc, middleAssoc, inputAssoc, incomingChargeAssoc, fullChannel]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

#print axioms fullIO_pentagon

end
end D5.S3.VertexAlgebra.LatticeSectorFullIOPentagon
