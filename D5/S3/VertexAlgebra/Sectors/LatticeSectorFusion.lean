/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized ground evaluation identifies the actual sector IO space with complex scalars. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorClassification

/-!
The normalization is the actual lattice cocycle coefficient of the true
creation series. This equivalence classifies all lawful mixed intertwiners;
it is not an ordinary vector-space tensor-product assertion. The classical
free-boson and lattice source attribution is retained in the suppliers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents MvPolynomial
noncomputable section

private theorem cocycle_nonzero (D : LatticeData) (α β : Charge D) : epsilon D α β ≠ 0 := by
  unfold epsilon paritySign
  split_ifs <;> norm_num

/-- Ground evaluation normalized by the actual nonzero lattice cocycle. -/
def groundEvaluation (D : LatticeData) (α β : Charge D) : IO D α β (α + β) →ₗ[ℂ] ℂ where
  toFun I := (epsilon D α β)⁻¹ * constantCoeff (I.val 1 (-bilinear D α β - 1) 1)
  map_add' I K := by simp [mul_add]
  map_smul' c I := by simp [mul_left_comm]

private theorem groundEvaluation_canonical (D : LatticeData) (α β : Charge D) :
    groundEvaluation D α β (canonicalIO D α β) = 1 := by
  change (epsilon D α β)⁻¹ * constantCoeff
    (canonical D α β 1 (-bilinear D α β - 1) 1) = 1
  rw [canonical_ground_normalization]
  simp [cocycle_nonzero D α β]

/-- Full nonsingular classification, with inverse c ↦ c times the actual J. -/
def classification (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) : IO D α β (α + β) ≃ₗ[ℂ] ℂ where
  toFun := groundEvaluation D α β
  invFun c := c • canonicalIO D α β
  map_add' := (groundEvaluation D α β).map_add
  map_smul' := (groundEvaluation D α β).map_smul
  left_inv I := by
    have normzero : groundEvaluation D α β
        (I - groundEvaluation D α β I • canonicalIO D α β) = 0 := by
      rw [map_sub, map_smul, groundEvaluation_canonical, smul_eq_mul, mul_one, sub_self]
    have zero : constantCoeff
        ((I - groundEvaluation D α β I • canonicalIO D α β).val
          1 (-bilinear D α β - 1) 1) = 0 := by
      exact (mul_eq_zero.mp normzero).resolve_left (inv_ne_zero (cocycle_nonzero D α β))
    exact (sub_eq_zero.mp
      (normalized_ground_detects_zero D H hHG hGH α β _ zero)).symm
  right_inv c := by
    rw [map_smul, groundEvaluation_canonical, smul_eq_mul, mul_one]

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
