/- GID: D5/S3/Quantum/Approximate/WeylStarCorrector
   generality: G
   mirror-B: D5/B/S3/Quantum/Approximate/WeylStarCorrector
   mirror-E: none(waiver:finite-diagonal-application)
   anchors: []
   utility: none
   digest: The normalized full Weyl diagonal gives dimension-free matrix star correction. -/

import D5.S3.Quantum.Approximate.FiniteStarNewton
import D5.S3.Observer.MatrixUnitCertificate
import D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Exact correction on every full complex matrix algebra

The diagonal uses all n-squared Weyl words with weight n to the power minus two.
Its algebraic tensor is the normalized matrix-unit diagonal. Every norm here is
the Euclidean L2 operator norm, and the involution is conjugate transpose.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct Matrix.Norms.L2Operator
open Matrix

namespace D5.S3.Quantum.Approximate
namespace WeylStarCorrector

open D5.S3.Observer.WindowRegister D5.S3.Observer.MatrixUnitCertificate
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Magic.SubspaceStabilizerEntropy
open D5.S3.Fourier.FinitePoisson

variable (n : ℕ) [NeZero n]

/-- The left leg retains the full adjoint, including the Weyl phase. -/
def leftLeg (p : ZMod n × ZMod n) : Matrix (ZMod n) (ZMod n) ℂ :=
  ((n : ℂ) ^ 2)⁻¹ • star (displacement n p.1 p.2)

/-- The right leg is the actual displacement word. -/
def rightLeg (p : ZMod n × ZMod n) : Matrix (ZMod n) (ZMod n) ℂ :=
  displacement n p.1 p.2

private lemma entry (a b i j : ZMod n) :
    displacement n a b i j = if i - j = a then ZMod.stdAddChar (b * j) else 0 := by
  rw [displacement, clockMatrix, Matrix.diagonal_pow, Matrix.mul_diagonal]
  simp only [Pi.pow_apply, shift_matrix_pow_apply, ZMod.natCast_zmod_val,
    clock_phase_pow_eq_character, character_apply]
  split_ifs <;> simp_all

private lemma pair_entry (i j k l : ZMod n) :
    ∑ p : ZMod n × ZMod n, leftLeg n p i j * rightLeg n p k l =
      if l = i ∧ k = j then (n : ℂ)⁻¹ else 0 := by
  classical
  simp only [leftLeg, rightLeg, Matrix.smul_apply, smul_eq_mul, Matrix.star_apply,
    entry, Fintype.sum_prod_type]
  have hc (b : ZMod n) :
      star (ZMod.stdAddChar (b * i) : ℂ) * ZMod.stdAddChar (b * l) =
        ZMod.stdAddChar (b * (l - i)) := by
    rw [show star (ZMod.stdAddChar (b * i) : ℂ) =
      ZMod.stdAddChar (-(b * i)) from (AddChar.map_neg_eq_conj _ _).symm]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  calc
    _ = ((n : ℂ) ^ 2)⁻¹ *
        (if k - l = j - i then ∑ b : ZMod n,
          star (ZMod.stdAddChar (b * i) : ℂ) * ZMod.stdAddChar (b * l) else 0) := by
      simp only [apply_ite star, star_zero, ite_mul, mul_ite, zero_mul, mul_zero,
        Finset.sum_ite_irrel]
      simp only [mul_assoc, ← Finset.mul_sum]
      by_cases h : k - l = j - i <;> simp [h, eq_comm]
    _ = ((n : ℂ) ^ 2)⁻¹ *
        (if k - l = j - i then
          (if l - i = 0 then (n : ℂ) else 0) else 0) := by
      simp_rw [hc]
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
      simp [ZMod.card]
    _ = _ := by
      by_cases hli : l = i
      · subst l
        by_cases hkj : k = j
        · subst k; simp; field_simp
        · have hsub : k - i ≠ j - i := by simpa using hkj
          simp [hsub, hkj]
      · simp [sub_ne_zero.mpr hli, hli]

private abbrev basis : Module.Basis (ZMod n × ZMod n) ℂ (Matrix (ZMod n) (ZMod n) ℂ) :=
  Matrix.stdBasis ℂ (ZMod n) (ZMod n)

private lemma basis_repr (X : Matrix (ZMod n) (ZMod n) ℂ) (i j : ZMod n) :
    (basis n).repr X (i, j) = X i j := by rfl

private lemma tensor_ext
    {s t : Matrix (ZMod n) (ZMod n) ℂ ⊗[ℂ] Matrix (ZMod n) (ZMod n) ℂ}
    (h : ∀ i j k l, ((basis n).tensorProduct (basis n)).repr s ((i, j), (k, l)) =
      ((basis n).tensorProduct (basis n)).repr t ((i, j), (k, l))) : s = t := by
  apply ((basis n).tensorProduct (basis n)).repr.injective
  ext ⟨⟨i, j⟩, ⟨k, l⟩⟩
  exact h i j k l

private def standardDiagonal :
    Matrix (ZMod n) (ZMod n) ℂ ⊗[ℂ] Matrix (ZMod n) (ZMod n) ℂ :=
  (n : ℂ)⁻¹ • ∑ i : ZMod n, ∑ j : ZMod n,
    Matrix.single i j (1 : ℂ) ⊗ₜ[ℂ] Matrix.single j i (1 : ℂ)

private lemma diagonal_identity :
    ∑ p : ZMod n × ZMod n, leftLeg n p ⊗ₜ[ℂ] rightLeg n p = standardDiagonal n := by
  classical
  apply tensor_ext n
  intro i j k l
  simp only [standardDiagonal, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    basis_repr, smul_eq_mul]
  simp_rw [mul_comm (rightLeg n _ k l)]
  rw [pair_entry]
  by_cases hi : i = l <;> by_cases hj : j = k <;>
    simp [Matrix.single_apply, ite_and, hi, hj, eq_comm]

private lemma diagonal_central (X : Matrix (ZMod n) (ZMod n) ℂ) :
    ∑ p : ZMod n × ZMod n, (X * leftLeg n p) ⊗ₜ[ℂ] rightLeg n p =
      ∑ p : ZMod n × ZMod n, leftLeg n p ⊗ₜ[ℂ] (rightLeg n p * X) := by
  classical
  let L : Matrix (ZMod n) (ZMod n) ℂ →ₗ[ℂ] Matrix (ZMod n) (ZMod n) ℂ :=
    LinearMap.mulLeft ℂ X
  let R : Matrix (ZMod n) (ZMod n) ℂ →ₗ[ℂ] Matrix (ZMod n) (ZMod n) ℂ :=
    LinearMap.mulRight ℂ X
  change ∑ p, TensorProduct.map L LinearMap.id (leftLeg n p ⊗ₜ[ℂ] rightLeg n p) =
    ∑ p, TensorProduct.map LinearMap.id R (leftLeg n p ⊗ₜ[ℂ] rightLeg n p)
  rw [← map_sum, ← map_sum, diagonal_identity]
  apply tensor_ext n
  intro i j k l
  simp only [standardDiagonal, map_smul, map_sum, TensorProduct.map_tmul,
    LinearMap.id_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, basis_repr, smul_eq_mul]
  by_cases hjk : j = k
  · subst k
    simp [L, R, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_comm]
  · simp [L, R, Matrix.mul_apply, Matrix.single_apply, ite_and, hjk]

private lemma word_norm (p : ZMod n × ZMod n) : ‖displacement n p.1 p.2‖ = 1 := by
  have h := displacement_unitary_pair p.1 p.2
  have hn := CStarRing.norm_star_mul_self (x := displacement n p.1 p.2)
  change ‖star (displacement n p.1 p.2) * displacement n p.1 p.2‖ = _ at hn
  rw [Matrix.star_eq_conjTranspose, h.1, norm_one] at hn
  nlinarith [norm_nonneg (displacement n p.1 p.2)]

/-- The full Weyl packet satisfies the product, tensor centrality and norm budget. -/
def diagonal : FiniteDiagonal (Matrix (ZMod n) (ZMod n) ℂ) (ZMod n × ZMod n) where
  left := leftLeg n
  right := rightLeg n
  product := by
    classical
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have he (p : ZMod n × ZMod n) : leftLeg n p * rightLeg n p =
        ((n : ℂ) ^ 2)⁻¹ • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
      rw [leftLeg, rightLeg, smul_mul_assoc, Matrix.star_eq_conjTranspose,
        displacement_unitary_pair p.1 p.2 |>.1]
    simp_rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have heq : (n * n : ℕ) * ((n : ℂ) ^ 2)⁻¹ = (1 : ℂ) := by
      push_cast
      field_simp
    rw [heq, one_smul]
  central := diagonal_central n
  budget := by
    classical
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    simp only [leftLeg, rightLeg, norm_smul, norm_star, word_norm n, mul_one,
      norm_inv, norm_pow, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, ZMod.card, nsmul_eq_mul, Nat.cast_mul]
    simpa only [pow_two] using le_of_eq (mul_inv_cancel₀ (pow_ne_zero 2 hn))

private def reindexEquiv : Matrix (ZMod n) (ZMod n) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ (ZMod.finEquiv n).toEquiv.symm with
    map_star' := fun X => rfl
    map_smul' := fun c X => map_smul
      (Matrix.reindexAlgEquiv ℂ ℂ (ZMod.finEquiv n).toEquiv.symm) c X }

private def finDiagonal : FiniteDiagonal (Matrix (Fin n) (Fin n) ℂ) (ZMod n × ZMod n) where
  left p := reindexEquiv n ((diagonal n).left p)
  right p := reindexEquiv n ((diagonal n).right p)
  product := by
    have h := congrArg (reindexEquiv n) (diagonal n).product
    simpa only [map_sum, map_mul, map_one] using h
  central X := by
    let e := reindexEquiv n
    have h := congrArg (TensorProduct.map e.toAlgEquiv.toLinearMap e.toAlgEquiv.toLinearMap)
      ((diagonal n).central (e.symm X))
    simpa only [map_sum, TensorProduct.map_tmul, StarAlgEquiv.coe_toAlgEquiv,
      AlgEquiv.toLinearMap_apply, map_mul, StarAlgEquiv.apply_symm_apply] using h
  budget := by
    simpa only [StarAlgEquiv.norm_map] using (diagonal n).budget

/-- Every positive matrix size uses the same constants and the full operator norm. -/
theorem exists_matrix_star_hom_close {A : Type*} [CStarAlgebra A]
    (f : Matrix (Fin n) (Fin n) ℂ →L[ℂ] A) {d : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 1 / 32) (hs : PreservesStar f)
    (hg : DefectBound f d) (hu : ‖f 1 - 1‖ ≤ 1 / 4) :
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] A,
      ∀ X, ‖ρ X - f X‖ ≤ (8 * d / 3) * ‖X‖ := by
  let : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  exact exists_star_hom_close (finDiagonal n) f hd hd' hs hg hu

end WeylStarCorrector
end D5.S3.Quantum.Approximate
