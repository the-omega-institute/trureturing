/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/UnitaryNorm
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Haar/UnitaryNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Haar.UnitaryNorm. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Haar/UnitaryNorm.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.HuaIntegral
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth (known
result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Hermitian involutions and real coordinates on skew-hermitian matrices. Operator norm and
determinant of elements of U(p,q). -/

/-- The complex matrix J is a hermitian involution: J* = J and J² = 1. -/
class IsHermInvolution {n} [Fintype n] (J :
  Matrix n n ℂ) where (isHermitian : J.IsHermitian) (mul_self : J * J = 1)

variable {n} [Fintype n] {J : Matrix n n ℂ} [IsHermInvolution J] (g : U J)

instance (ε : n → _) : IsHermInvolution (signMatrix ε) :=
  ⟨by simp [signMatrix, Matrix.IsHermitian], signMatrix_mul_self ε⟩

instance : @IsHermInvolution n _ 1 := ⟨by simp, by simp⟩

lemma IsHermInvolution.det_ne_zero (J : Matrix n n ℂ) [IsHermInvolution J] : J.det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse mul_self

/-- The real linear map sending a real matrix y to the skew-hermitian matrix with entries i·y_aa
on the diagonal and ((1+i)y_ab − (1−i)y_ba)/√2 off it. -/
noncomputable def skewOfReal :
  Matrix n n ℝ →ₗ[ℝ] Matrix n n ℂ := by use! (fun y ↦ Matrix.of fun a b ↦ ((1 +
  Complex.I) * y a b - (1 - Complex.I) * y b a) / ite (a = b) 2 √2) <;> simp [funext_iff] <;> grind

/-- The real linear map sending a complex matrix x to the real matrix with entries Re x_ab + Im
x_ab, divided by √2 off the diagonal; a left inverse of `skewOfReal`. -/
noncomputable def skewCoords : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℝ := by use! (fun x ↦
  Matrix.of fun a b ↦ ((x a b).re + (x a b).im) / ite (a = b) 1 √2) <;> simp [funext_iff] <;> grind

lemma IsHermInvolution.isUnit : IsUnit J := .of_mul_eq_one _ mul_self

lemma IsHermInvolution.mem_unitary :
  J ∈ _root_.unitary _ := by simp [Unitary.mem_iff, isHermitian.star_eq, mul_self]

@[simp] lemma U.norm_det : ‖g.1.1.det‖ = 1 :=
  CStarRing.norm_coe_unitary (det (IsHermInvolution.det_ne_zero J).isUnit g)

open CStarRing Matrix.Norms.L2Operator

lemma U.norm_inv : ‖g⁻¹.1.1‖ = ‖g.1.1‖ := by simp [↓coe_inv IsHermInvolution.mul_self,
  norm_mul_mem_unitary,
  norm_mem_unitary_mul, IsHermInvolution.mem_unitary, Matrix.l2_opNorm_conjTranspose]

lemma U.one_le_norm [Nonempty n] : 1 ≤ ‖g.1.1‖ := by
  simpa [← pow_two, ↓norm_inv] using norm_mul_le g⁻¹.1.1 g
