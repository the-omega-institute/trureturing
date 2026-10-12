/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoFixedFieldEquiv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryRankTwoCoordinates

namespace NikolovSegal.UnitaryRankTwo

open Matrix NikolovSegal.UnitaryField
variable {F : Type*} [Field F] [Finite F]

/-- An explicit actual group equivalence for any nonzero anti-fixed scaling element. -/
def coordinateEquiv (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0) (hanti : ι τ = -τ) :
    specialUnitary ι ≃* SpecialLinearGroup (Fin 2) (fixedField ι) where
  toFun := toFixedSL ι τ hτ hanti
  invFun := fromFixedSL ι τ hτ hanti
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    change coordinateMatrix τ⁻¹
      ((fixedCoordinateMatrix ι τ hτ hanti A).map (fixedField ι).subtype) = A.val.val
    rw [fixedCoordinateMatrix_coe, coordinateMatrix_inverse τ hτ]
  right_inv B := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change coordinateMatrix τ
      (coordinateMatrix τ⁻¹ (B.val.map (fixedField ι).subtype)) i j = (B.val i j : F)
    have hh := coordinateMatrix_inverse τ⁻¹ (inv_ne_zero hτ)
      (B.val.map (fixedField ι).subtype)
    simpa only [inv_inv, Matrix.map_apply, Subfield.subtype_apply] using congrArg (fun M => M i j) hh
  map_mul' := (toFixedSL ι τ hτ hanti).map_mul

theorem coordinateEquiv_backward (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0)
    (hanti : ι τ = -τ) (B : SpecialLinearGroup (Fin 2) (fixedField ι)) :
    ((coordinateEquiv ι τ hτ hanti).symm B).val.val =
      !![(B.val 0 0 : F), τ * (B.val 0 1 : F);
         (B.val 1 0 : F) / τ, (B.val 1 1 : F)] := by
  change coordinateMatrix τ⁻¹ (B.val.map (fixedField ι).subtype) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, div_eq_mul_inv, mul_comm]

end NikolovSegal.UnitaryRankTwo
