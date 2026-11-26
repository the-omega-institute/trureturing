/- GID: D5/S3/Quantum/Schatten/GramDeterminantCauchySchwarz
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/GramDeterminantCauchySchwarz
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For complex m×k matrices U, V, |det(U*V)|² ≤ det(U*U) det(V*V). -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#179)
escape_witness: gram_cauchy_schwarz (form (2), the public conclusion). Cauchy–Binet identifies
  det(UᴴV), det(UᴴU), det(VᴴV) with the minor sums Σ conj(u_T) v_T, Σ |u_T|², Σ |v_T|²
  (the last two via conj(z) z = |z|²); the triangle inequality and the finite
  Cauchy–Schwarz inequality then bound the mixed sum. No prerequisite states any Gram
  determinant bound, so the chain is an estimate across three separate facts, not an
  instantiation. The structurally similar private MalkounJordanElementary.gram_det_le is
  labelled bind-only there under an open-problem-resolution basis, where the label did
  not decide admission; it proves a different, real-part bound for equal Gram matrices.
proof_shape:
  gram_cauchy_schwarz: content.
Direct frozen dependency: D5/S3/Quantum/Schatten/CompoundMatrices (cauchyBinet), module
  statement_id sha256:8398f8b23ac0815231125a1304c91754b658ebb26e9e24af0ace9c2147f696ce.
Search: D5 has the private MalkounJordanElementary.gram_det_le (equal Gram matrices, real
part only) and Matrix.det_mul_transpose_self_submatrix_le in
D5/S3/Arith/AbsoluteValues/Heights/Hadamard (column deletion over an ordered field); neither
states this bound. Pinned Mathlib has no matrix Cauchy–Binet; exteriorPower.inner_ιMulti_ιMulti
gives the Gram-determinant inner product for real spaces only (its RCLike generalization is
a TODO), and cross_dot_cross is the three-dimensional Binet–Cauchy identity.
-/

import D5.S3.Quantum.Schatten.CompoundMatrices

/-! # The Gram-determinant Cauchy–Schwarz inequality

For complex `m × k` matrices `U` and `V`, `|det(UᴴV)|² ≤ det(UᴴU) det(VᴴV)`, the right
side being real and nonnegative. All `m` and `k` are allowed: for `k = 0` both sides are `1`, and
for `k > m` both Gram determinants vanish.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.Schatten.GramDeterminantCauchySchwarz

open Matrix
open scoped ComplexOrder

/-- `|det(UᴴV)|² ≤ det(UᴴU) det(VᴴV)` in the complex order, for all complex `m × k`
matrices `U` and `V`. -/
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
  have normSq_eq (w : {S : Finset (Fin m) // S.card = k} → ℂ)
      (S : {S : Finset (Fin m) // S.card = k}) :
      star (w S) * w S = ((‖w S‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have huu : (Uᴴ * U).det = ((∑ S, ‖u S‖ ^ 2 : ℝ) : ℂ) := by
    rw [cb U U, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun S _ => normSq_eq u S)
  have hvv : (Vᴴ * V).det = ((∑ S, ‖v S‖ ^ 2 : ℝ) : ℂ) := by
    rw [cb V V, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun S _ => normSq_eq v S)
  have huv : ‖(Uᴴ * V).det‖ ≤ ∑ S, ‖u S‖ * ‖v S‖ := by
    rw [cb U V]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun S _ => ?_)))
    rw [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun S => ‖u S‖) (fun S => ‖v S‖)
  rw [huu, hvv, ← Complex.ofReal_mul, Complex.real_le_real]
  calc ‖(Uᴴ * V).det‖ ^ 2 ≤ (∑ S, ‖u S‖ * ‖v S‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) huv 2
    _ ≤ _ := hcs

end D5.S3.Quantum.Schatten.GramDeterminantCauchySchwarz
