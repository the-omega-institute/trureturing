/- GID: D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/OperatorWielandtNormRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.claim; result=D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.result; claim=D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.claim
   digest: A unital 2-positive map refutes the operator Wielandt product norm bound. -/

/- Source: Minghua Lin, arXiv:1212.5690v1, §3, Conjecture 3.4.
   escape_witness: the 4×4 matrices A,P,Y and Φ(Z)=PZP*+YZY*, with
     ‖T e₂‖² = 5/4 > ((M−m)/(M+m))⁴ for m=1/25 and M=13.
   Direct frozen dependencies: none (pinned Mathlib only).
   admission_basis: open-problem-resolution (#16004; Refuted)
   Per-declaration proof_shape and live consumers:
     IsPartialIsometry: definition; consumers=claim, geometry
     IsUnitalTwoPositive: definition; consumers=claim, two_positive
     NormLE: definition; consumers=claim, norm_failure
     claim: definition; consumer=result
     A: definition; consumers=lower, upper, images, result
     P: definition; consumers=Φ, geometry, two_positive, images, determinants, product, result
     Y: definition; consumers=Φ, geometry, two_positive, images, determinants, product, result
     L: definition; consumer=lower
     U: definition; consumer=upper
     Φ: definition; consumers=two_positive, images, determinants, product, result
     lower: bind-only; consumer=result
     upper: bind-only; consumer=result
     geometry: bind-only; consumer=result
     two_positive: bind-only; consumer=result
     D: definition; consumers=images, inverse_D, determinants
     Q: definition; consumers=inverse_D, product
     B: definition; consumers=images, product
     T: definition; consumers=product, norm_failure
     images: bind-only; consumers=determinants, product
     inverse_D: bind-only; consumer=product
     determinants: bind-only; consumer=result
     product: bind-only; consumer=result
     norm_failure: bind-only; consumer=result
     result: bind-only; consumer=external open-problem resolution. -/

import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxRecDepth 16384
set_option maxHeartbeats 800000

noncomputable section
open scoped ComplexOrder
open Matrix
namespace D5.S3.Quantum.Matrix.OperatorWielandtNormRefutation

/-- A partial isometry: `X X* X = X`. -/
def IsPartialIsometry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Prop := X * Xᴴ * X = X
/-- A unital 2-positive linear map (definition on p. 6). -/
def IsUnitalTwoPositive {n k : ℕ}
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ) : Prop :=
  Φ 1 = 1 ∧ ∀ A B C : Matrix (Fin n) (Fin n) ℂ,
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef →
      (Matrix.fromBlocks (Φ A) (Φ B) (Φ Bᴴ) (Φ C)).PosSemidef
/-- `‖T‖ ≤ c` for the operator norm induced by the Euclidean norm. -/
def NormLE {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (c : ℝ) : Prop :=
  ∀ v : EuclideanSpace ℂ (Fin k), ‖(Matrix.toEuclideanLin T) v‖ ≤ c * ‖v‖
/-- Conjecture 3.4 on finite-dimensional spaces with genuine inverses. -/
def claim : Prop :=
  ∀ (n k : ℕ) (A X Y : Matrix (Fin n) (Fin n) ℂ) (m M : ℝ)
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ),
    0 < m → m ≤ M → A.IsHermitian →
    (A - (m : ℂ) • 1).PosSemidef → ((M : ℂ) • 1 - A).PosSemidef →
    IsPartialIsometry X → IsPartialIsometry Y → Xᴴ * Y = 0 →
    IsUnitalTwoPositive Φ →
    IsUnit (Φ (Yᴴ * A * Y)).det → IsUnit (Φ (Xᴴ * A * X)).det →
    NormLE (Φ (Xᴴ * A * Y) * (Φ (Yᴴ * A * Y))⁻¹ * Φ (Yᴴ * A * X) *
      (Φ (Xᴴ * A * X))⁻¹) (((M - m) / (M + m)) ^ 2)

private def A : Matrix (Fin 4) (Fin 4) ℂ :=
  !![9,0,2,0; 0,2,1,0; 2,1,1,0; 0,0,0,1]
private def P : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1,1,0,0]
private def Y : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0]
private def L : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 25/112,25/49,1,0; 0,0,0,1]
private def U : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; -1/2,-1/11,1,0; 0,0,0,1]
private def Φ : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun Z := P * Z * Pᴴ + Y * Z * Yᴴ
  map_add' Z W := by simp [Matrix.mul_add, Matrix.add_mul, add_add_add_comm]
  map_smul' c Z := by simp [smul_add]

private lemma lower : (A - (1/25 : ℂ) • 1).PosSemidef := by
  have hd : (diagonal (![224/25,49/25,33/9800,24/25] : Fin 4 → ℂ)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  convert hd.mul_mul_conjTranspose_same L using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, L, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, map_ofNat]

private lemma upper : ((13 : ℂ) • 1 - A).PosSemidef := by
  have hd : (diagonal (![4,11,120/11,12] : Fin 4 → ℂ)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  convert hd.mul_mul_conjTranspose_same U using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, U, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, map_ofNat]

private lemma geometry : IsPartialIsometry P ∧ IsPartialIsometry Y ∧ Pᴴ * Y = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change P * Pᴴ * P = P
    simp only [P, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num
  · change Y * Yᴴ * Y = Y
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Y, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Fin.reduceFinMk, Matrix.cons_val_two,
        Matrix.cons_val_three, Fin.ext_iff, map_ofNat]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [P, Y, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fin.reduceFinMk,
        Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, map_ofNat]

private lemma two_positive : IsUnitalTwoPositive Φ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Φ, P, Y, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, Matrix.one_apply, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, map_ofNat]
  · intro B C D h
    have hp := h.mul_mul_conjTranspose_same (fromBlocks P 0 0 P)
    have hy := h.mul_mul_conjTranspose_same (fromBlocks Y 0 0 Y)
    convert hp.add hy using 1
    simp [Φ, fromBlocks_multiply, fromBlocks_conjTranspose, ← fromBlocks_add]

private def D : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![9,2,9,2]
private def Q : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![1/9,1/2,1/9,1/2]
private def B : Matrix (Fin 4) (Fin 4) ℂ :=
  !![2,0,0,0; 1,0,0,0; 0,0,2,0; 0,0,1,0]
private def T : Matrix (Fin 4) (Fin 4) ℂ :=
  !![4/9,1,0,0; 2/9,1/2,0,0; 0,0,4/9,1; 0,0,2/9,1/2]

private lemma images : Φ (Yᴴ * A * Y) = 1 ∧ Φ (Pᴴ * A * P) = D ∧
    Φ (Pᴴ * A * Y) = B ∧ Φ (Yᴴ * A * P) = Bᴴ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    dsimp only [Φ] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, A, P, Y, D, B, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.add_apply, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.cons_val_zero', Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      map_ofNat, map_zero, map_one, star_zero, star_one, zero_mul, mul_zero,
      one_mul, mul_one, zero_add, add_zero, ite_true, ite_false, Fin.ext_iff]
  all_goals norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk, Fin.ext_iff, map_ofNat]

private lemma inverse_D : D⁻¹ = Q := by
  apply Matrix.inv_eq_right_inv
  simp only [D, Q, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

private lemma determinants : (Φ (Yᴴ * A * Y)).det = 1 ∧
    (Φ (Pᴴ * A * P)).det = 324 := by
  rw [images.1, images.2.1]
  norm_num [D, Matrix.det_diagonal, Fin.prod_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk]

private lemma product : Φ (Pᴴ * A * Y) * (Φ (Yᴴ * A * Y))⁻¹ *
    Φ (Yᴴ * A * P) * (Φ (Pᴴ * A * P))⁻¹ = T := by
  rw [images.1, images.2.1, images.2.2.1, images.2.2.2, inverse_D]
  simp only [inv_one, Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num only [Matrix.of_apply, B, Q, T, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ', Matrix.cons_val_zero', Fin.val_zero, Fin.val_one, Fin.val_ofNat,
      map_ofNat, map_zero, map_one, star_zero, star_one, zero_mul, mul_zero,
      one_mul, mul_one, zero_add, add_zero, ite_true, ite_false, Fin.ext_iff]
  all_goals norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk, Fin.ext_iff, map_ofNat]

private lemma norm_failure : ¬ NormLE T (((13 - (1/25 : ℝ)) / (13 + 1/25)) ^ 2) := by
  intro h
  let v : EuclideanSpace ℂ (Fin 4) := EuclideanSpace.single 1 1
  have hv : ‖v‖ = 1 := by simp [v]
  have ht : ‖Matrix.toEuclideanLin T v‖ ^ 2 = (5/4 : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [T, v, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, PiLp.single_apply, Fin.reduceFinMk, Matrix.cons_val_two,
      Matrix.cons_val_three, Fin.ext_iff]
  have hh := h v
  rw [hv] at hh
  norm_num at hh
  have hn := norm_nonneg (Matrix.toEuclideanLin T v)
  nlinarith

theorem result : ¬ claim := by
  intro h
  have ha : A.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, Matrix.conjTranspose_apply, Fin.reduceFinMk, Matrix.cons_val_two,
        Matrix.cons_val_three, map_ofNat]
  have hd := determinants
  have hout := h 4 4 A P Y (1/25) 13 Φ (by norm_num) (by norm_num) ha
    (by simpa using lower) (by simpa using upper) geometry.1 geometry.2.1
    geometry.2.2 two_positive (by rw [hd.1]; exact isUnit_one)
    (by rw [hd.2]; exact isUnit_iff_ne_zero.mpr (by norm_num))
  rw [product] at hout
  exact norm_failure hout

end D5.S3.Quantum.Matrix.OperatorWielandtNormRefutation
