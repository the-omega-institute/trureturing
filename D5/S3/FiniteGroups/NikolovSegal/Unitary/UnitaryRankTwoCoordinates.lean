/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryRankTwoGeometry

namespace NikolovSegal.UnitaryRankTwo

open Matrix NikolovSegal.UnitaryField
variable {F : Type*} [Field F]

/-- Change of basis by diag(τ,1): D⁻¹ A D. -/
def coordinateMatrix (τ : F) (A : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F := !![A 0 0, A 0 1 / τ; τ * A 1 0, A 1 1]

theorem coordinateMatrix_conjugation (τ : F) (hτ : τ ≠ 0) (A : Matrix (Fin 2) (Fin 2) F) :
    coordinateMatrix τ A = diagonal ![τ⁻¹, 1] * A * diagonal ![τ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, mul_diagonal, diagonal_mul, div_eq_mul_inv, mul_comm, mul_assoc, hτ]

theorem coordinateMatrix_det (τ : F) (hτ : τ ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) F) : (coordinateMatrix τ A).det = A.det := by
  rw [coordinateMatrix_conjugation τ hτ, det_mul, det_mul, det_diagonal, det_diagonal]
  simp [Fin.prod_univ_two, hτ, mul_assoc, mul_comm, mul_left_comm]

theorem coordinateMatrix_mul (τ : F) (hτ : τ ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) F) :
    coordinateMatrix τ (A * B) = coordinateMatrix τ A * coordinateMatrix τ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, mul_apply, Fin.sum_univ_two] <;>
    field_simp [hτ] <;> ring

theorem coordinateMatrix_inverse (τ : F) (hτ : τ ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) F) :
    coordinateMatrix τ⁻¹ (coordinateMatrix τ A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coordinateMatrix, hτ]

def scaleSL (τ : F) (hτ : τ ≠ 0) :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F where
  toFun A := ⟨coordinateMatrix τ A.val, (coordinateMatrix_det τ hτ A.val).trans A.property⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinateMatrix]
  map_mul' A B := Subtype.ext (coordinateMatrix_mul τ hτ A.val B.val)

@[simp] theorem scaleSL_val (τ : F) (hτ : τ ≠ 0) (A : SpecialLinearGroup (Fin 2) F) :
    (scaleSL τ hτ A).val = coordinateMatrix τ A.val := rfl

variable [Finite F]

/-- Each entry of the changed SU2 basis lies in the actual fixed subfield. -/
theorem coordinateMatrix_fixed (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0)
    (hanti : ι τ = -τ) (A : specialUnitary ι) (i j : Fin 2) :
    ι (coordinateMatrix τ A.val.val i j) = coordinateMatrix τ A.val.val i j := by
  obtain ⟨h00, h11, h01, h10⟩ := (hermitian_iff_entries ι A.val).mp A.property
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix, map_div₀, hanti, h00, h11, h01, h10]

/-- The literal fixed-field coordinate matrix, with membership proved entry by entry. -/
def fixedCoordinateMatrix (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0)
    (hanti : ι τ = -τ) (A : specialUnitary ι) :
    Matrix (Fin 2) (Fin 2) (fixedField ι) := fun i j =>
  ⟨coordinateMatrix τ A.val.val i j,
    (mem_fixedField ι _).mpr (coordinateMatrix_fixed ι τ hτ hanti A i j)⟩

@[simp] theorem fixedCoordinateMatrix_coe (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0)
    (hanti : ι τ = -τ) (A : specialUnitary ι) :
    (fixedCoordinateMatrix ι τ hτ hanti A).map (fixedField ι).subtype =
      coordinateMatrix τ A.val.val := rfl

/-- Actual SU2 → native SL2 over its fixed field. -/
def toFixedSL (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0) (hanti : ι τ = -τ) :
    specialUnitary ι →* SpecialLinearGroup (Fin 2) (fixedField ι) where
  toFun A := ⟨fixedCoordinateMatrix ι τ hτ hanti A, by
    apply (fixedField ι).subtype.injective
    rw [RingHom.map_det]
    change (coordinateMatrix τ A.val.val).det = 1
    rw [coordinateMatrix_det τ hτ]
    exact A.val.property⟩
  map_one' := by
    apply Subtype.ext
    change fixedCoordinateMatrix ι τ hτ hanti 1 = (1 : Matrix (Fin 2) (Fin 2) (fixedField ι))
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    fin_cases i <;> fin_cases j <;> simp [fixedCoordinateMatrix, coordinateMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change fixedCoordinateMatrix ι τ hτ hanti (A * B) =
      fixedCoordinateMatrix ι τ hτ hanti A * fixedCoordinateMatrix ι τ hτ hanti B
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change coordinateMatrix τ (A.val.val * B.val.val) i j =
      ((fixedCoordinateMatrix ι τ hτ hanti A * fixedCoordinateMatrix ι τ hτ hanti B) i j : F)
    rw [coordinateMatrix_mul τ hτ]
    simp [mul_apply, fixedCoordinateMatrix, Fin.sum_univ_two]

/-- Inclusion into F followed by the inverse actual change of basis. -/
def fromFixedSL (ι : F ≃+* F) (τ : F) (hτ : τ ≠ 0) (hanti : ι τ = -τ)
    (B : SpecialLinearGroup (Fin 2) (fixedField ι)) : specialUnitary ι :=
  ⟨scaleSL τ⁻¹ (inv_ne_zero hτ) (SpecialLinearGroup.map (fixedField ι).subtype B), by
    apply (hermitian_iff_entries ι _).mpr
    have hf (i j : Fin 2) : ι (B.val i j : F) = B.val i j :=
      (mem_fixedField ι _).mp (B.val i j).property
    change ι (B.val 0 0 : F) = (B.val 0 0 : F) ∧
      ι (B.val 1 1 : F) = (B.val 1 1 : F) ∧
      ι ((B.val 0 1 : F) / τ⁻¹) = -((B.val 0 1 : F) / τ⁻¹) ∧
      ι (τ⁻¹ * (B.val 1 0 : F)) = -(τ⁻¹ * (B.val 1 0 : F))
    simp [hf, hanti, map_div₀]
    ⟩

end NikolovSegal.UnitaryRankTwo
