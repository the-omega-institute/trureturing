/- GID: D5/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/KerrSchildWeylDoubleCopy4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null rank-one metric identities and the projective Weyl quartic of the Coulomb square. -/

import D5.S3.Geometry.Lorentz.WeylNullScreen
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Pointwise Kerr–Schild algebra and the Coulomb square in the Weyl screen convention. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.KerrSchildWeylDoubleCopy4D

open Matrix Polynomial
open WeylNullScreen (minkowski STF3 Weyl4 WeylQuartic weyl_electric_magnetic_equiv
  weylQuarticEquiv weylQuarticEquiv_eval quarticEval complexTide)

abbrev Vector4 := Fin 4 → ℝ

def eta : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![-1, 1, 1, 1]

def sharp (k : Vector4) : Vector4 := ![-k 0, k 1, k 2, k 3]

theorem eta_square : eta * eta = 1 := by
  rw [eta, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

theorem eta_sharp (k : Vector4) : eta *ᵥ k = sharp k := by
  funext i
  rw [eta, mulVec_diagonal]
  fin_cases i <;> simp [sharp]

theorem vec_eta (k : Vector4) : k ᵥ* eta = sharp k := by
  funext i
  rw [eta, vecMul_diagonal]
  fin_cases i <;> simp [sharp]

theorem sharp_dot (k : Vector4) : sharp k ⬝ᵥ k = minkowski k k := by
  simp [sharp, dotProduct, minkowski, Fin.sum_univ_four]

private theorem eta_raise_sharp (k : Vector4) : eta *ᵥ sharp k = k := by
  rw [← eta_sharp, mulVec_mulVec, eta_square, one_mulVec]

private theorem sharp_vec_eta (k : Vector4) : sharp k ᵥ* eta = k := by
  rw [← vec_eta, vecMul_vecMul, eta_square, vecMul_one]

def ksMetric (φ : ℝ) (k : Vector4) : Matrix (Fin 4) (Fin 4) ℝ :=
  eta + φ • vecMulVec k k

def ksInverse (φ : ℝ) (k : Vector4) : Matrix (Fin 4) (Fin 4) ℝ :=
  eta - φ • vecMulVec (sharp k) (sharp k)

theorem ks_inverse (φ : ℝ) (k : Vector4) (hnull : minkowski k k = 0) :
    ksMetric φ k * ksInverse φ k = 1 ∧ ksInverse φ k * ksMetric φ k = 1 := by
  have hn : sharp k ⬝ᵥ k = 0 := (sharp_dot k).trans hnull
  have hn' : k ⬝ᵥ sharp k = 0 := (dotProduct_comm _ _).trans hn
  constructor
  · rw [ksMetric, ksInverse, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp [smul_mul_assoc, mul_smul_comm, eta_square, mul_vecMulVec, vecMulVec_mul,
      vecMulVec_mulVec, vec_eta, eta_raise_sharp, hn']
  · rw [ksMetric, ksInverse, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
    simp [smul_mul_assoc, mul_smul_comm, eta_square, mul_vecMulVec, vecMulVec_mul,
      vecMulVec_mulVec, eta_sharp, sharp_vec_eta, hn]

theorem ks_det (φ : ℝ) (k : Vector4) (hnull : minkowski k k = 0) :
    (ksMetric φ k).det = -1 := by
  have hη : eta.det = -1 := by norm_num [eta, det_diagonal, Fin.prod_univ_succ]
  have hprod : eta * ksMetric φ k = 1 + vecMulVec (φ • sharp k) k := by
    rw [ksMetric, Matrix.mul_add, eta_square, mul_smul_comm, mul_vecMulVec, eta_sharp]
    congr 1
    ext i j
    simp [vecMulVec_apply, Pi.smul_apply, mul_assoc]
  have hn : k ⬝ᵥ (φ • sharp k) = 0 := by
    rw [dotProduct_smul, dotProduct_comm k (sharp k), sharp_dot, hnull, smul_zero]
  have hd : (eta * ksMetric φ k).det = 1 := by
    rw [hprod, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, hn, add_zero]
  rw [det_mul, hη, neg_one_mul] at hd
  exact neg_eq_iff_eq_neg.mp hd

/-- The symmetric trace-free part of an electric field's outer square, divided by the scale. -/
def electricSquare (E : Fin 3 → ℝ) (scale : ℝ) : STF3 ℝ := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    scale⁻¹ • (vecMulVec E E - ((∑ i, E i * E i) / 3) • 1)
  refine ⟨A, fun i j => ?_, ?_⟩
  · by_cases h : i = j
    · subst j
      rfl
    · simp [A, vecMulVec_apply, h, Ne.symm h, mul_comm]
  · change (∑ i : Fin 3, (1 : ℝ) * A i i) = 0
    simp [A, vecMulVec_apply, Fin.sum_univ_three]
    ring

def schwarzschildElectric (M r : ℝ) : STF3 ℝ := by
  let d : Fin 3 → ℝ := ![-(M / r ^ 3), -(M / r ^ 3), 2 * (M / r ^ 3)]
  refine ⟨diagonal d, fun i j => ?_, ?_⟩
  · by_cases h : i = j
    · subst j
      rfl
    · simp [h, Ne.symm h]
  · change (∑ i : Fin 3, (1 : ℝ) * diagonal d i i) = 0
    simp [d, Fin.sum_univ_three]
    ring

def schwarzschildWeyl (M r : ℝ) : Weyl4 :=
  weyl_electric_magnetic_equiv.symm (schwarzschildElectric M r, 0)

def coulombElectric (Q r : ℝ) : Fin 3 → ℝ := ![0, 0, Q / r ^ 2]

def coulombScale (M Q r : ℝ) : ℝ := -Q ^ 2 / (3 * M * r)

/-- With the negative scalar scale, the raw STF square has the opposite curvature sign. -/
theorem coulomb_raw_square (M Q r : ℝ) (hM : M ≠ 0) (hQ : Q ≠ 0) (hr : r ≠ 0) :
    electricSquare (coulombElectric Q r) (coulombScale M Q r) = -schwarzschildElectric M r := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [electricSquare, coulombElectric, coulombScale, schwarzschildElectric,
      Fin.sum_univ_three] <;>
    field_simp <;> norm_num

/-- The Coulomb square with the curvature sign of the chosen Schwarzschild tide. -/
def coulombDoubleCopy (M Q r : ℝ) : STF3 ℝ :=
  -electricSquare (coulombElectric Q r) (coulombScale M Q r)

theorem coulomb_to_schwarzschild_stf (M Q r : ℝ) (hM : M ≠ 0) (hQ : Q ≠ 0) (hr : r ≠ 0) :
    coulombDoubleCopy M Q r = schwarzschildElectric M r := by
  rw [coulombDoubleCopy, coulomb_raw_square M Q r hM hQ hr, neg_neg]

theorem schwarzschild_weylQuartic (M r : ℝ) :
    (weylQuarticEquiv (schwarzschildWeyl M r)).val =
      Polynomial.monomial 2 ((24 : ℂ) * (M / r ^ 3 : ℝ)) := by
  let a : ℂ := ⟨-(M / r ^ 3), -(0 : ℝ)⟩
  let b : ℂ := ⟨0, -(0 : ℝ)⟩
  let c : ℂ := (24 : ℂ) * (M / r ^ 3 : ℝ)
  let p : WeylQuartic := ⟨monomial 2 c, monomial_coe_mem_degreeLT (2 : Fin 5) c⟩
  change (weylQuarticEquiv (schwarzschildWeyl M r)).val = p.val
  apply congrArg Subtype.val
  apply (Polynomial.degreeLTEquiv ℂ 5).injective
  rw [show weylQuarticEquiv (schwarzschildWeyl M r) =
      (Polynomial.degreeLTEquiv ℂ 5).symm
        ![2 * (a - a) + 4 * Complex.I * b, -8 * b - 8 * Complex.I * b,
          -12 * (a + a), 8 * b - 8 * Complex.I * b, 2 * (a - a) - 4 * Complex.I * b] from rfl,
    LinearEquiv.apply_symm_apply]
  funext i
  change _ = (monomial 2 c).coeff (i : ℕ)
  have ha : a = -Complex.ofReal (M / r ^ 3) := by
    rw [← Complex.ofReal_neg]
    change Complex.mk _ (-(0 : ℝ)) = Complex.mk _ 0
    rw [neg_zero]
  have hb : b = 0 := by apply Complex.ext <;> simp [b]
  rw [ha, hb]
  fin_cases i <;> norm_num [coeff_monomial, c] <;> ring

theorem schwarzschild_tide_eval (M r : ℝ) (z : ℂ) :
    complexTide (schwarzschildWeyl M r).val (some z) = 24 * (M / r ^ 3 : ℝ) * z ^ 2 ∧
    complexTide (schwarzschildWeyl M r).val none = 0 := by
  rw [← weylQuarticEquiv_eval, ← weylQuarticEquiv_eval]
  constructor
  · change (weylQuarticEquiv (schwarzschildWeyl M r)).val.eval z = _
    rw [schwarzschild_weylQuartic, eval_monomial]
  · change (weylQuarticEquiv (schwarzschildWeyl M r)).val.coeff 4 = 0
    rw [schwarzschild_weylQuartic]
    simp [coeff_monomial]

/-- Homogenize the polynomial to degree four. Independent linear factors give distinct
projective roots, including the root at infinity when a factor is constant on the finite chart. -/
def IsTypeD (p : WeylQuartic) : Prop :=
  p ≠ 0 ∧ ∃ a₀ b₀ a₁ b₁ C : ℂ, C ≠ 0 ∧ a₀ * b₁ - a₁ * b₀ ≠ 0 ∧
    p.val = Polynomial.C C * (Polynomial.C a₀ * X - Polynomial.C b₀) ^ 2 *
      (Polynomial.C a₁ * X - Polynomial.C b₁) ^ 2

theorem schwarzschild_is_type_D (M r : ℝ) (hM : M ≠ 0) (hr : r ≠ 0) :
    IsTypeD (weylQuarticEquiv (schwarzschildWeyl M r)) := by
  let c : ℂ := 24 * (M / r ^ 3 : ℝ)
  have hc : c ≠ 0 := mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr (div_ne_zero hM (pow_ne_zero _ hr)))
  refine ⟨?_, 1, 0, 0, 1, c, hc, by norm_num, ?_⟩
  · intro hzero
    have hp := congrArg (fun p : WeylQuartic => p.val.coeff 2) hzero
    change (weylQuarticEquiv (schwarzschildWeyl M r)).val.coeff 2 = 0 at hp
    rw [schwarzschild_weylQuartic, coeff_monomial_same] at hp
    exact hc hp
  · rw [schwarzschild_weylQuartic, ← C_mul_X_pow_eq_monomial]
    simp [c]

end D5.S3.Geometry.Lorentz.KerrSchildWeylDoubleCopy4D
