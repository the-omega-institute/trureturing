/- GID: D5/S3/Quantum/Matrix/DivisionFreeSchur
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/DivisionFreeSchur
   mirror-E: none(waiver:algebraic-positivity)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Singular-safe Schur minors and their mixed polarization preserve real matrix positivity. -/

/-
proof_shape: schur_posSemidef, mixed_posSemidef: content
admission_basis: escape-witness
escape_witness: A quadratic discriminant and a scalar square decomposition
  prove the mixed cross-matrix inequality without invertibility assumptions.
Consumers: RankFourLength28Purity.certificate_nonnegative.
The private Cauchy and expansion helpers are consumed proof organization.
Escape audit evidence remains uncompiled; see issues 17689 and 17734.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

open Matrix
namespace D5.S3.Quantum.Matrix.DivisionFreeSchur

variable {I J : Type*} [Fintype I] [Fintype J]

def quadratic (K : Matrix I I ℝ) (v : I → ℝ) : ℝ := v ⬝ᵥ (K *ᵥ v)

def compressed (K : Matrix I I ℝ) (U : Matrix I J ℝ) : Matrix J J ℝ :=
  Uᵀ * K * U

def cross (K : Matrix I I ℝ) (v : I → ℝ) (U : Matrix I J ℝ) : J → ℝ :=
  Uᵀ *ᵥ (K *ᵥ v)

def schur (K : Matrix I I ℝ) (v : I → ℝ) (U : Matrix I J ℝ) : Matrix J J ℝ :=
  quadratic K v • compressed K U - vecMulVec (cross K v U) (cross K v U)

def mixed (K₀ K₁ : Matrix I I ℝ) (v : I → ℝ) (U : Matrix I J ℝ) : Matrix J J ℝ :=
  quadratic K₀ v • compressed K₁ U + quadratic K₁ v • compressed K₀ U -
    vecMulVec (cross K₀ v U) (cross K₁ v U) -
    vecMulVec (cross K₁ v U) (cross K₀ v U)

private theorem bilinear_symm {K : Matrix I I ℝ} (hK : K.IsHermitian) (v w : I → ℝ) :
    v ⬝ᵥ (K *ᵥ w) = w ⬝ᵥ (K *ᵥ v) := by
  have ht : Kᵀ = K := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.eq
  simpa only [ht] using Matrix.dotProduct_transpose_mulVec K v w

private theorem cauchy {K : Matrix I I ℝ} (hK : K.PosSemidef) (v w : I → ℝ) :
    (v ⬝ᵥ (K *ᵥ w)) ^ 2 ≤ quadratic K v * quadratic K w := by
  have hpoly (t : ℝ) :
      0 ≤ quadratic K v * (t * t) + (2 * (v ⬝ᵥ (K *ᵥ w))) * t + quadratic K w := by
    have h := hK.dotProduct_mulVec_nonneg (t • v + w)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h
    rw [bilinear_symm hK.isHermitian w v] at h
    dsimp only [quadratic]
    nlinarith only [h]
  have h := discrim_le_zero hpoly
  dsimp only [discrim] at h
  nlinarith only [h]

private theorem compressed_quadratic (K : Matrix I I ℝ) (U : Matrix I J ℝ) (z : J → ℝ) :
    quadratic (compressed K U) z = quadratic K (U *ᵥ z) := by
  unfold quadratic compressed
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]

private theorem cross_dot (K : Matrix I I ℝ) (v : I → ℝ)
    (U : Matrix I J ℝ) (z : J → ℝ) :
    z ⬝ᵥ cross K v U = (U *ᵥ z) ⬝ᵥ (K *ᵥ v) := by
  exact Matrix.dotProduct_transpose_mulVec U z (K *ᵥ v)

private theorem quadratic_add (A B : Matrix J J ℝ) (z : J → ℝ) :
    quadratic (A+B) z = quadratic A z + quadratic B z := by
  simp [quadratic, Matrix.add_mulVec, dotProduct_add]

private theorem quadratic_sub (A B : Matrix J J ℝ) (z : J → ℝ) :
    quadratic (A-B) z = quadratic A z - quadratic B z := by
  simp [quadratic, Matrix.sub_mulVec, dotProduct_sub]

private theorem quadratic_smul (a : ℝ) (A : Matrix J J ℝ) (z : J → ℝ) :
    quadratic (a • A) z = a * quadratic A z := by
  simp [quadratic, Matrix.smul_mulVec, dotProduct_smul]

private theorem outer_quadratic (a b z : J → ℝ) :
    quadratic (vecMulVec a b) z = (z ⬝ᵥ a) * (z ⬝ᵥ b) := by
  simp [quadratic, dotProduct, Matrix.mulVec, Matrix.vecMulVec,
    Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

private theorem schur_quadratic {K : Matrix I I ℝ} (hK : K.IsHermitian)
    (v : I → ℝ) (U : Matrix I J ℝ) (z : J → ℝ) :
    quadratic (schur K v U) z = quadratic K v * quadratic K (U *ᵥ z) -
      (v ⬝ᵥ (K *ᵥ (U *ᵥ z))) ^ 2 := by
  simp only [schur, quadratic_sub, quadratic_smul, compressed_quadratic,
    outer_quadratic, cross_dot]
  rw [bilinear_symm hK (U *ᵥ z) v]
  ring

/-- The undivided Schur minor is positive even when the pivot is zero. -/
theorem schur_posSemidef {K : Matrix I I ℝ} (hK : K.PosSemidef)
    (v : I → ℝ) (U : Matrix I J ℝ) : (schur K v U).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hc : (compressed K U).IsHermitian := by
      simpa only [compressed, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (hK.conjTranspose_mul_mul_same U).isHermitian
    have hb : (vecMulVec (cross K v U) (cross K v U)).IsHermitian := by
      simpa only [star_trivial] using
        (Matrix.posSemidef_vecMulVec_self_star (cross K v U)).isHermitian
    exact (hc.smul (by simp)).sub hb
  · intro z
    change 0 ≤ quadratic (schur K v U) z
    rw [schur_quadratic hK.isHermitian]
    exact sub_nonneg.mpr (cauchy hK v (U *ᵥ z))

private theorem mixed_scalar {q₀ q₁ d₀ d₁ b₀ b₁ : ℝ}
    (hq₀ : 0 ≤ q₀) (hq₁ : 0 ≤ q₁) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (h₀ : b₀ ^ 2 ≤ q₀ * d₀) (h₁ : b₁ ^ 2 ≤ q₁ * d₁) :
    0 ≤ q₀ * d₁ + q₁ * d₀ - 2 * b₀ * b₁ := by
  have hp : b₀ ^ 2 * b₁ ^ 2 ≤ (q₀ * d₀) * (q₁ * d₁) :=
    mul_le_mul h₀ h₁ (sq_nonneg b₁) (mul_nonneg hq₀ hd₀)
  have he : 0 ≤ q₀ * d₁ + q₁ * d₀ :=
    add_nonneg (mul_nonneg hq₀ hd₁) (mul_nonneg hq₁ hd₀)
  by_contra h
  have hb : 0 < 2 * b₀ * b₁ := by linarith
  have hs := sq_nonneg (q₀ * d₁ - q₁ * d₀)
  have hstrict : (q₀ * d₁ + q₁ * d₀) ^ 2 < (2 * b₀ * b₁) ^ 2 := by
    nlinarith [mul_pos (show 0 < 2*b₀*b₁ - (q₀*d₁+q₁*d₀) by linarith)
      (show 0 < 2*b₀*b₁ + (q₀*d₁+q₁*d₀) by linarith)]
  nlinarith only [hp, hs, hstrict]

private theorem mixed_quadratic {K₀ K₁ : Matrix I I ℝ}
    (h₀ : K₀.IsHermitian) (h₁ : K₁.IsHermitian)
    (v : I → ℝ) (U : Matrix I J ℝ) (z : J → ℝ) :
    quadratic (mixed K₀ K₁ v U) z =
      quadratic K₀ v * quadratic K₁ (U *ᵥ z) +
      quadratic K₁ v * quadratic K₀ (U *ᵥ z) -
      2 * (v ⬝ᵥ (K₀ *ᵥ (U *ᵥ z))) * (v ⬝ᵥ (K₁ *ᵥ (U *ᵥ z))) := by
  simp only [mixed, quadratic_sub, quadratic_add, quadratic_smul,
    compressed_quadratic, outer_quadratic, cross_dot]
  rw [bilinear_symm h₀ (U *ᵥ z) v, bilinear_symm h₁ (U *ᵥ z) v]
  ring

/-- Polarization across two different PSD matrices needs neither a common
factorization nor a positive pivot. -/
theorem mixed_posSemidef {K₀ K₁ : Matrix I I ℝ}
    (h₀ : K₀.PosSemidef) (h₁ : K₁.PosSemidef)
    (v : I → ℝ) (U : Matrix I J ℝ) : (mixed K₀ K₁ v U).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hc₀ : (compressed K₀ U).IsHermitian := by
      simpa only [compressed, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (h₀.conjTranspose_mul_mul_same U).isHermitian
    have hc₁ : (compressed K₁ U).IsHermitian := by
      simpa only [compressed, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (h₁.conjTranspose_mul_mul_same U).isHermitian
    have hb : (vecMulVec (cross K₀ v U) (cross K₁ v U) +
        vecMulVec (cross K₁ v U) (cross K₀ v U)).IsHermitian := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.vecMulVec, add_comm, mul_comm]
    have he : mixed K₀ K₁ v U =
        (quadratic K₀ v • compressed K₁ U + quadratic K₁ v • compressed K₀ U) -
        (vecMulVec (cross K₀ v U) (cross K₁ v U) +
          vecMulVec (cross K₁ v U) (cross K₀ v U)) := by
      unfold mixed
      abel
    rw [he]
    exact ((hc₁.smul (by simp)).add (hc₀.smul (by simp))).sub hb
  · intro z
    change 0 ≤ quadratic (mixed K₀ K₁ v U) z
    rw [mixed_quadratic h₀.isHermitian h₁.isHermitian]
    exact mixed_scalar
      (by simpa [quadratic] using h₀.dotProduct_mulVec_nonneg v)
      (by simpa [quadratic] using h₁.dotProduct_mulVec_nonneg v)
      (by simpa [quadratic] using h₀.dotProduct_mulVec_nonneg (U *ᵥ z))
      (by simpa [quadratic] using h₁.dotProduct_mulVec_nonneg (U *ᵥ z))
      (cauchy h₀ v (U *ᵥ z)) (cauchy h₁ v (U *ᵥ z))

end D5.S3.Quantum.Matrix.DivisionFreeSchur
