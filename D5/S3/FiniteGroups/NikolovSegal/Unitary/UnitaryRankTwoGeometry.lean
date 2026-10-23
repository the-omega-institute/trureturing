/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryRankTwoGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryAntidiagonalCoordinates

/-! The literal determinant-one unitary group for the split Hermitian form in rank two.
The entry recognition uses the native SL2 inverse, not a recognition premise. -/
namespace NikolovSegal.UnitaryRankTwo

open Matrix NikolovSegal.UnitaryField
variable {F : Type*} [Field F]

abbrev J : Matrix (Fin 2) (Fin 2) F := antiDiagonal 2

theorem J_eq : (J : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_antifixed (ι : F ≃+* F) (hinv : Function.Involutive ι)
    (hne : ι ≠ RingEquiv.refl F) : ∃ τ : F, τ ≠ 0 ∧ ι τ = -τ := by
  have hn : ∃ x : F, ι x ≠ x := by
    by_contra h
    apply hne
    ext x
    exact not_ne_iff.mp (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hn
  refine ⟨x - ι x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv x]
  ring

theorem adjoint_mul (ι : F ≃+* F) (A B : Matrix (Fin 2) (Fin 2) F) :
    adjoint ι (A * B) = adjoint ι B * adjoint ι A := by
  simp only [adjoint, transpose_mul, Matrix.map_mul]

theorem hermitian_iff_inverse (ι : F ≃+* F) (A : SpecialLinearGroup (Fin 2) F) :
    adjoint ι A.val * J * A.val = J ↔ adjoint ι A.val * J = J * (A⁻¹).val := by
  have hright : A.val * (A⁻¹).val = 1 := by
    exact congrArg Subtype.val (mul_inv_cancel A)
  have hleft : (A⁻¹).val * A.val = 1 := by
    exact congrArg Subtype.val (inv_mul_cancel A)
  constructor
  · intro h
    calc
      adjoint ι A.val * J = (adjoint ι A.val * J) * (A.val * (A⁻¹).val) := by
        rw [hright, Matrix.mul_one]
      _ = J * (A⁻¹).val := by rw [← Matrix.mul_assoc, h]
  · intro h
    rw [h, Matrix.mul_assoc, hleft, Matrix.mul_one]

theorem inverse_matrix (A : SpecialLinearGroup (Fin 2) F) :
    (A⁻¹).val = !![A.val 1 1, -A.val 0 1; -A.val 1 0, A.val 0 0] := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  rfl

theorem hermitian_iff_entries (ι : F ≃+* F) (A : SpecialLinearGroup (Fin 2) F) :
    adjoint ι A.val * J * A.val = J ↔
      ι (A.val 0 0) = A.val 0 0 ∧ ι (A.val 1 1) = A.val 1 1 ∧
      ι (A.val 0 1) = -A.val 0 1 ∧ ι (A.val 1 0) = -A.val 1 0 := by
  rw [hermitian_iff_inverse, inverse_matrix]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [adjoint, J_eq, mul_apply, Fin.sum_univ_two,
        Matrix.mul_fin_two] using congrArg (fun B => B 0 1) h
    · simpa [adjoint, J_eq, mul_apply, Fin.sum_univ_two,
        Matrix.mul_fin_two] using congrArg (fun B => B 1 0) h
    · simpa [adjoint, J_eq, mul_apply, Fin.sum_univ_two,
        Matrix.mul_fin_two] using congrArg (fun B => B 1 1) h
    · simpa [adjoint, J_eq, mul_apply, Fin.sum_univ_two,
        Matrix.mul_fin_two] using congrArg (fun B => B 0 0) h
  · rintro ⟨h00, h11, h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adjoint, J_eq, mul_apply, Fin.sum_univ_two,
        Matrix.mul_fin_two, h00, h11, h01, h10]

/-- Actual SU2 for the Hermitian anti-diagonal, as a subgroup of native SL2. -/
def specialUnitary (ι : F ≃+* F) : Subgroup (SpecialLinearGroup (Fin 2) F) where
  carrier := {A | adjoint ι A.val * J * A.val = J}
  one_mem' := by simp [adjoint]
  mul_mem' := by
    intro A B hA hB
    change adjoint ι (A.val * B.val) * J * (A.val * B.val) = J
    rw [adjoint_mul]
    calc
      (adjoint ι B.val * adjoint ι A.val) * J * (A.val * B.val) =
          adjoint ι B.val * (adjoint ι A.val * J * A.val) * B.val := by
        simp only [Matrix.mul_assoc]
      _ = J := by rw [hA]; exact hB
  inv_mem' := by
    intro A hA
    obtain ⟨h00, h11, h01, h10⟩ := (hermitian_iff_entries ι A).mp hA
    apply (hermitian_iff_entries ι (A⁻¹)).mpr
    rw [inverse_matrix]
    simp [h00, h11, h01, h10]

@[simp] theorem mem_specialUnitary (ι : F ≃+* F) (A : SpecialLinearGroup (Fin 2) F) :
    A ∈ specialUnitary ι ↔ adjoint ι A.val * antiDiagonal 2 * A.val = antiDiagonal 2 := Iff.rfl

end NikolovSegal.UnitaryRankTwo
