import OmegaMath.Matrix.HomogeneousWordPowers

/-! Omega original.

The square of the size-three skew-symmetric matrix space is full, including
after independent invertible left and right multiplication. -/

compile_only_with_mathlib

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace OmegaMath.HomogeneousWordPowers

section SizeThreeAlternating

variable {K : Type*} [Field K]

local notation "Mat" => Matrix (Fin 3) (Fin 3) K

private def E (i j : Fin 3) : Mat := Matrix.single i j (1 : K)

private def skewSpace : Submodule K Mat where
  carrier := {A | A.transpose = -A}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A.transpose = -A at hA
    change B.transpose = -B at hB
    change (A + B).transpose = -(A + B)
    rw [Matrix.transpose_add, hA, hB]
    abel
  smul_mem' := by
    intro c A hA
    simpa [Matrix.transpose_smul, smul_neg] using congrArg (c • ·) hA

private def skewGenerator (i j : Fin 3) : Mat :=
  E i j - E j i

private theorem skewGenerator_mem (i j : Fin 3) :
    skewGenerator (K := K) i j ∈ skewSpace (K := K) := by
  change (skewGenerator i j).transpose = -skewGenerator i j
  simp [skewGenerator, E, sub_eq_add_neg, neg_add_rev]

private theorem E_mul_E_same (i j k : Fin 3) :
    E (K := K) i j * E j k = E i k := by
  simp [E]

private theorem E_mul_E_ne (i j k l : Fin 3) (h : j ≠ k) :
    E (K := K) i j * E k l = 0 := by
  simpa [E] using Matrix.single_mul_single_of_ne (1 : K) i j k h (1 : K)

private theorem skew_product_offdiag (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    skewGenerator (K := K) i j * skewGenerator j k = E i k := by
  change (E i j - E j i) * (E j k - E k j) = E i k
  simp only [sub_mul, mul_sub]
  rw [E_mul_E_same, E_mul_E_ne i j k j hjk,
    E_mul_E_ne j i j k hij, E_mul_E_ne j i k j hik]
  simp

private theorem skew_product_diag (i j : Fin 3) (hij : i ≠ j) :
    skewGenerator (K := K) i j * skewGenerator j i =
      E i i + E j j := by
  change (E i j - E j i) * (E j i - E i j) = E i i + E j j
  simp only [sub_mul, mul_sub]
  rw [E_mul_E_same, E_mul_E_ne i j i j hij.symm,
    E_mul_E_ne j i j i hij, E_mul_E_same]
  simp

private theorem skew_square_mem {X Y Z : Mat} (h : X = Y * Z)
    (hY : Y ∈ skewSpace) (hZ : Z ∈ skewSpace) : X ∈ skewSpace ^ 2 := by
  rw [h]
  simpa [pow_two] using Submodule.mul_mem_mul hY hZ

private theorem skew_square_contains_diag [NeZero (2 : K)] (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    E (K := K) i i ∈ skewSpace ^ 2 := by
  have hpair (a b : Fin 3) (hab : a ≠ b) : E (K := K) a a + E b b ∈ skewSpace ^ 2 :=
    skew_square_mem (skew_product_diag a b hab).symm
      (skewGenerator_mem a b) (skewGenerator_mem b a)
  have h := (skewSpace (K := K) ^ 2).sub_mem
    ((skewSpace ^ 2).add_mem (hpair i j hij) (hpair i k hik)) (hpair j k hjk)
  have he : (E (K := K) i i + E j j) + (E i i + E k k) - (E j j + E k k) =
      (2 : K) • E i i := by
    rw [two_smul]
    abel
  rw [he] at h
  simpa [smul_smul, two_ne_zero] using
    (skewSpace (K := K) ^ 2).smul_mem (2 : K)⁻¹ h

private theorem skew_space_sq_eq_top [NeZero (2 : K)] :
    (skewSpace (K := K)) ^ 2 = ⊤ := by
  have hthird (i j : Fin 3) (hij : i ≠ j) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩
  have hunit (i j : Fin 3) : E (K := K) i j ∈ skewSpace ^ 2 := by
    by_cases hij : i = j
    · subst j
      have hnext : i + 1 ≠ i := by fin_cases i <;> decide
      obtain ⟨k, hki, hkj⟩ := hthird i (i + 1) hnext.symm
      exact skew_square_contains_diag i (i + 1) k hnext.symm hki.symm hkj.symm
    · obtain ⟨k, hki, hkj⟩ := hthird i j hij
      exact skew_square_mem (skew_product_offdiag i k j hki.symm hkj hij).symm
        (skewGenerator_mem i k) (skewGenerator_mem k j)
  apply top_unique
  intro X _
  refine Matrix.induction_on' X (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) ?_
  intro i j x
  simpa [E] using (skewSpace (K := K) ^ 2).smul_mem x (hunit i j)

private def transposeUnit (T : Matˣ) : Matˣ where
  val := (T : Mat)ᵀ
  inv := (↑T⁻¹ : Mat)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

private theorem skew_congruence_mem (T : Matˣ) {X : Mat}
    (hX : X ∈ skewSpace) : (T : Mat) * X * (T : Mat)ᵀ ∈ skewSpace := by
  change X.transpose = -X at hX
  change ((T : Mat) * X * (T : Mat)ᵀ).transpose = -((T : Mat) * X * (T : Mat)ᵀ)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hX]
  simp [mul_assoc]

/-- Independent invertible left and right multipliers preserve fullness of the
square of the full size-three skew-symmetric space. -/
theorem alternating_left_right_square_eq_top [NeZero (2 : K)]
    (L : Submodule K Mat) (P Q : Matˣ)
    (hclass : ∀ C : Mat, C.transpose = -C ↔
      ∃ B ∈ L, (P : Mat) * B * (Q : Mat) = C) :
    L ^ 2 = ⊤ := by
  let T : Matˣ := Q⁻¹ * P⁻¹
  let e := (P.mulLeftLinearEquiv K Mat).trans
    ((Q * transposeUnit T).mulRightLinearEquiv K)
  have hle : (skewSpace (K := K)) ^ 2 ≤ (L ^ 2).map e.toLinearMap := by
    rw [pow_two]
    apply Submodule.mul_le.2
    intro X hX Y hY
    let Z : Mat := (↑T⁻¹ : Mat) * Y * (↑T⁻¹ : Mat)ᵀ
    have hZ : Z ∈ skewSpace := skew_congruence_mem T⁻¹ hY
    obtain ⟨B, hB, hBX⟩ := (hclass X).mp hX
    obtain ⟨C, hC, hCZ⟩ := (hclass Z).mp hZ
    refine Submodule.mem_map.mpr ⟨B * C, ?_, ?_⟩
    · simpa [pow_two] using Submodule.mul_mem_mul hB hC
    · change (P : Mat) * (B * C) * ((Q : Mat) * (T : Mat)ᵀ) = X * Y
      have hmid : (Q : Mat) * (T : Mat) * (P : Mat) = 1 := by
        change (((Q * T * P : Matˣ) : Mat)) = 1
        simp [T]
      have hright : (↑T⁻¹ : Mat)ᵀ * (T : Mat)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      calc
        _ = ((P : Mat) * B * (Q : Mat)) * (T : Mat) *
            ((P : Mat) * C * (Q : Mat)) * (T : Mat)ᵀ := by
              calc
                _ = (P : Mat) * (B * (((Q : Mat) * (T : Mat) * (P : Mat)) * C)) *
                    ((Q : Mat) * (T : Mat)ᵀ) := by rw [hmid, one_mul]
                _ = _ := by simp only [mul_assoc]
        _ = X * Y := by
          rw [hBX, hCZ]
          change X * (T : Mat) * ((↑T⁻¹ : Mat) * Y * (↑T⁻¹ : Mat)ᵀ) * (T : Mat)ᵀ =
            X * Y
          calc
            _ = X * (((T : Mat) * (↑T⁻¹ : Mat)) * Y) *
                ((↑T⁻¹ : Mat)ᵀ * (T : Mat)ᵀ) := by simp only [mul_assoc]
            _ = _ := by rw [Units.mul_inv, one_mul, hright, mul_one]
  rw [skew_space_sq_eq_top] at hle
  exact Submodule.map_eq_top_iff.mp (top_unique hle)

end SizeThreeAlternating
end OmegaMath.HomogeneousWordPowers
