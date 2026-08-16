/- GID: D5/S3/PrimeForms/Crossing/ThirdOrderIntegrality
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/ThirdOrderIntegrality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: K-conjugation is integral exactly on a single mod-three congruence class. -/

import D5.S3.PrimeForms.Crossing.ThirdOrderReciprocity

open Matrix

namespace D5.S3.PrimeForms.Crossing.ThirdOrderIntegrality

open ThirdOrderReciprocity

/-- **Third-order integrality criterion (E.73).** Since `det K = 3`, the matrix
`K * gamma * adjugate K` is the numerator of the rational conjugate `K * gamma * K⁻¹`.
All four numerator entries are divisible by `3` exactly when the entries of `gamma` satisfy the
single congruence `a + 2b + c + 2d = 0 (mod 3)`. -/
theorem k_conjugate_integral_iff (gamma : Matrix (Fin 2) (Fin 2) ℤ) :
    (∀ i j, (3 : ℤ) ∣ (K * gamma * adjugate K) i j) ↔
      (3 : ℤ) ∣ gamma 0 0 + 2 * gamma 0 1 + gamma 1 0 + 2 * gamma 1 1 := by
  constructor
  · intro h
    rcases h 0 0 with ⟨q, hq⟩
    refine ⟨gamma 1 0 + 2 * gamma 1 1 - q, ?_⟩
    simp [K, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] at hq
    linear_combination -hq
  · rintro ⟨q, hq⟩ i j
    fin_cases i <;> fin_cases j
    · refine ⟨gamma 1 0 + 2 * gamma 1 1 - q, ?_⟩
      simp [K, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two]
      linear_combination -hq
    · refine ⟨gamma 0 0 + gamma 0 1 - gamma 1 0 - q, ?_⟩
      simp [K, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two]
      linear_combination -hq
    · refine ⟨q - gamma 0 0 - 2 * gamma 0 1, ?_⟩
      simp [K, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two]
      linear_combination hq
    · refine ⟨q + gamma 0 0 - gamma 1 0 - gamma 1 1, ?_⟩
      simp [K, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two]
      linear_combination hq

#print axioms k_conjugate_integral_iff

end D5.S3.PrimeForms.Crossing.ThirdOrderIntegrality
