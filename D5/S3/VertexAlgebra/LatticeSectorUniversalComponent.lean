/- GID: D5/S3/VertexAlgebra/LatticeSectorUniversalComponent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSectorUniversalComponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit representing intertwiner equivalence for an arbitrary target sector. -/

import D5.S3.VertexAlgebra.LatticeSectorHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
noncomputable section

/-- Postcomposition with the actual canonical mixed intertwiner. -/
def componentForward (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ : Charge D) : SectorHom D (α + β) γ →ₗ[ℂ] IO D α β γ where
  toFun f := post D H hHG hGH α β (α + β) γ f (canonicalIO D α β)
  map_add' f g := by
    apply Subtype.ext; apply LinearMap.ext; intro u; funext n
    apply LinearMap.ext; intro v
    rfl
  map_smul' c f := by
    apply Subtype.ext; apply LinearMap.ext; intro u; funext n
    apply LinearMap.ext; intro v
    rfl

/-- Explicit inverse: the matching-charge scalar identity, and zero elsewhere. -/
def componentBackward (D : LatticeData) (α β γ : Charge D)
    (I : IO D α β γ) : SectorHom D (α + β) γ := by
  classical
  by_cases h : γ = α + β
  · subst γ
    exact scalarHom D (α + β) (groundEvaluation D α β I)
  · exact 0

private theorem forward_scalar (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (c : ℂ) :
    componentForward D H hHG hGH α β (α + β) (scalarHom D (α + β) c) =
      c • canonicalIO D α β := by
  apply Subtype.ext; apply LinearMap.ext; intro u; funext n
  apply LinearMap.ext; intro v
  rfl

/-- The explicit inverse is a right inverse on the full IO space. -/
theorem component_right_inverse (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ : Charge D) (I : IO D α β γ) :
    componentForward D H hHG hGH α β γ (componentBackward D α β γ I) = I := by
  classical
  by_cases h : γ = α + β
  · subst γ
    simp only [componentBackward, dite_true]
    rw [forward_scalar]
    exact (classification D H hHG hGH α β).symm_apply_apply I
  · have hz := wrong_charge_vanishing D H hHG α β γ h I
    simp [componentBackward, h, hz]

/-- The explicit inverse recovers every actual module morphism. -/
theorem component_left_inverse (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ : Charge D) (f : SectorHom D (α + β) γ) :
    componentBackward D α β γ (componentForward D H hHG hGH α β γ f) = f := by
  classical
  by_cases h : γ = α + β
  · subst γ
    obtain ⟨c, rfl⟩ := hom_scalar D H hHG hGH (α + β) f
    simp only [componentBackward, dite_true, forward_scalar]
    have h := (classification D H hHG hGH α β).apply_symm_apply c
    change groundEvaluation D α β (c • canonicalIO D α β) = c at h
    rw [h]
  · rw [hom_wrong_charge D H hHG hGH (α + β) γ h f]
    simp [componentBackward, h]

/-- Genuine sector-target universal property, with both explicit inverse laws. -/
def componentUniversal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ : Charge D) : SectorHom D (α + β) γ ≃ₗ[ℂ] IO D α β γ where
  toLinearMap := componentForward D H hHG hGH α β γ
  invFun := componentBackward D α β γ
  left_inv := component_left_inverse D H hHG hGH α β γ
  right_inv := component_right_inverse D H hHG hGH α β γ

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
