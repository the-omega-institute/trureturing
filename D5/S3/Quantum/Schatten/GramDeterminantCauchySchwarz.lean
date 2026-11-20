/- GID: D5/S3/Quantum/Schatten/GramDeterminantCauchySchwarz
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/GramDeterminantCauchySchwarz
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For complex m×k matrices U, V, |det(U*V)|² ≤ det(U*U) det(V*V). -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#179)
escape_witness: gram_cauchy_schwarz (the public conclusion; Cauchy–Binet expands the three
  Gram determinants over k-row minors, and the triangle inequality with the finite
  Cauchy–Schwarz inequality bounds the mixed sum)
proof_shape:
  gram_cauchy_schwarz: content.
Direct frozen dependency: D5/S3/Quantum/Schatten/CompoundMatrices (cauchyBinet).
Search: MalkounJordanElementary has the private gram_det_le, which assumes equal Gram
matrices and bounds only the real part of det(U*V) by det(U*U); it does not give the
modulus-squared product bound for arbitrary U, V. Hadamard.det_mul_transpose_self_submatrix_le
compares Gram determinants under column deletion. No Mathlib Gram-determinant Cauchy–Schwarz
or Cauchy–Binet declaration was found in the pinned tree.
-/

import D5.S3.Quantum.Schatten.CompoundMatrices

/-! # The Gram-determinant Cauchy–Schwarz inequality

For complex `m × k` matrices `U` and `V`, `|det(UᴴV)|² ≤ det(UᴴU) det(VᴴV)`, the right side
being real and nonnegative. All `m` and `k` are allowed: for `k = 0` both sides are `1`, and
for `k > m` both Gram determinants vanish.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.GramDeterminantCauchySchwarz

open _root_.Matrix Finset
open scoped ComplexOrder

/-- `|det(UᴴV)|² ≤ det(UᴴU) det(VᴴV)` in the complex order, for every `m × k` complex `U, V`. -/
theorem gram_cauchy_schwarz {m k : ℕ} (U V : Matrix (Fin m) (Fin k) ℂ) :
    ((‖(Uᴴ * V).det‖ ^ 2 : ℝ) : ℂ) ≤ (Uᴴ * U).det * (Vᴴ * V).det := by
  classical
  let u (S : {S : Finset (Fin m) // S.card = k}) : ℂ :=
    (U.submatrix (S.1.orderEmbOfFin S.2) id).det
  let v (S : {S : Finset (Fin m) // S.card = k}) : ℂ :=
    (V.submatrix (S.1.orderEmbOfFin S.2) id).det
  have cb (A B : Matrix (Fin m) (Fin k) ℂ) :
      (Aᴴ * B).det = ∑ S : {S : Finset (Fin m) // S.card = k},
        star ((A.submatrix (S.1.orderEmbOfFin S.2) id).det) *
          (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    simpa only [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose] using
      (cauchyBinet Aᴴ B)
  have self (w : {S : Finset (Fin m) // S.card = k} → ℂ) (S : {S : Finset (Fin m) // S.card = k}) :
      star (w S) * w S = ((‖w S‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have huu : (Uᴴ * U).det = ((∑ S, ‖u S‖ ^ 2 : ℝ) : ℂ) := by
    rw [cb U U, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun S _ => self u S)
  have hvv : (Vᴴ * V).det = ((∑ S, ‖v S‖ ^ 2 : ℝ) : ℂ) := by
    rw [cb V V, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun S _ => self v S)
  have huv : ‖(Uᴴ * V).det‖ ≤ ∑ S, ‖u S‖ * ‖v S‖ := by
    rw [cb U V]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun S _ => ?_)))
    rw [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun S => ‖u S‖) (fun S => ‖v S‖)
  rw [huu, hvv, ← Complex.ofReal_mul, Complex.real_le_real]
  calc ‖(Uᴴ * V).det‖ ^ 2 ≤ (∑ S, ‖u S‖ * ‖v S‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) huv 2
    _ ≤ _ := hcs

end D5.S3.Quantum.Matrix.GramDeterminantCauchySchwarz
