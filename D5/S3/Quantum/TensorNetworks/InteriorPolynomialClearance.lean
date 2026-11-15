/- GID: D5/S3/Quantum/TensorNetworks/InteriorPolynomialClearance
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorPolynomialClearance
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: Division-free native inverse-transfer recurrences with exact row factors. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Native, division-free adjugate recurrences; no positivity of inverse transfer is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
open Matrix
open scoped Matrix ComplexOrder
open PeriodicMPSParentIntersection (Bond)
open OpenBoundaryMPSInteriorRootRealization

def d (s : Sector) : ℝ := Complex.normSq (delta s)
def a0 (s : Sector) : ℝ := 1 + Complex.normSq s.lambda
def a1 (s : Sector) : ℝ := 1 + Complex.normSq s.mu
def kappa (s : Sector) : ℝ := Complex.normSq (1 + star s.lambda * s.mu)
def schurMass (s : Sector) : ℝ := a0 s * a1 s * kappa s
def Gamma (s : Sector) : ℝ := d s * schurMass s
def cL (s : Sector) (p : ℕ) (z : ℂ) : ℝ :=
  Gamma s ^ (2*p) * Complex.normSq z ^ (2*p)
def cR (s : Sector) (q : ℕ) (z : ℂ) : ℝ :=
  Gamma s ^ (2*q) * d s ^ 4 * Complex.normSq z ^ (2*q+4)

def adjugateTwo {R : Type*} [CommRing R] (a b z : R) : Matrix (Fin 2) (Fin 2) R :=
  !![b*z, -z; -a, 1]

def schurWeights {R : Type*} [CommRing R] (u v ub vb : R) : Matrix (Fin 2) (Fin 2) R :=
  let A := 1+u*ub
  let B := 1+v*vb
  let e := 1+ub*v
  let f := 1+u*vb
  !![B*(e*f), A*B*e; A*B*f, A*(e*f)]

def J (s : Sector) (z : ℂ) : Bond := adjugateTwo (alpha s) (beta s) z
def W (s : Sector) : Bond := schurWeights s.lambda s.mu (star s.lambda) (star s.mu)
def Wstar (s : Sector) : Bond := (W s)ᵀ

def leftStep (s : Sector) (z : ℂ) (X : Bond) : Bond :=
  fun i j => Wstar s i j * ((J s z)ᴴ * X * J s z) i j
def rightStep (s : Sector) (z : ℂ) (X : Bond) : Bond :=
  J s z * (W s ⊙ X) * (J s z)ᴴ
def leftNumerator (s : Sector) (z : ℂ) (p : ℕ) (P : Bond) : Bond :=
  (leftStep s z)^[p] P
def rightNumerator (s : Sector) (z : ℂ) (q : ℕ) (H : Bond) : Bond :=
  (rightStep s z)^[q] (J s z ^ 2 * H * (J s z ^ 2)ᴴ)

private lemma mass (s : Sector) :
    (schurMass s : ℂ) = (1+s.lambda*star s.lambda)*(1+s.mu*star s.mu)*
      ((1+star s.lambda*s.mu)*(1+s.lambda*star s.mu)) := by
  have h : (1+star s.lambda*s.mu)*(1+s.lambda*star s.mu) = (kappa s : ℂ) := by
    have hc : star (1+star s.lambda*s.mu) = 1+s.lambda*star s.mu := by
      simp [star_add, star_mul, mul_comm]
    rw [← hc, RCLike.star_def, Complex.mul_conj]
    rfl
  rw [h]
  simp [schurMass, a0, a1, RCLike.star_def, Complex.mul_conj]

private lemma weights_clear (s : Sector) (hs : Regular s) (X : Bond) :
    (fun i j => W s i j * X i j) = (schurMass s : ℂ) • diagonalInverse s X := by
  have hc : 1+star s.lambda*s.mu ≠ 0 := Complex.normSq_pos.mp hs.2
  have hc' : 1+s.lambda*star s.mu ≠ 0 := by
    simpa [star_add, star_mul, mul_comm] using star_ne_zero.mpr hc
  have hn (u : ℂ) : 1+u*star u ≠ 0 := by
    rw [RCLike.star_def, Complex.mul_conj]
    exact_mod_cast (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg u)))
  have hn' (u : ℂ) : 1+star u*u ≠ 0 := by simpa [mul_comm] using hn u
  simp only [RCLike.star_def] at hn hn' hc hc'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, schurWeights, diagonalInverse, mass, hn, hc, hc'] <;>
    field_simp [hn, hn', hc, hc', RCLike.star_def] <;> ring

private lemma weights_star_clear (s : Sector) (hs : Regular s) (X : Bond) :
    (fun i j => Wstar s i j * X i j) = (schurMass s : ℂ) • diagonalStarInverse s X := by
  ext i j
  have h := congrFun (congrFun (weights_clear s hs Xᵀ) j) i
  simpa [Wstar, diagonalInverse, diagonalStarInverse, mul_comm] using h

private lemma adjugate_inverse (s : Sector) (hs : Regular s) (z : ℂ) (hz : z ≠ 0) :
    J s z = (delta s*z) • (G s z)⁻¹ := by
  have hd : delta s ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs.1).1).1
  have hdet : (G s z).det = delta s*z := by
    simp [G, delta, alpha, beta, det_fin_two]; ring
  rw [Matrix.inv_def, hdet, Ring.inverse_eq_inv, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero hd hz), one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, adjugateTwo, G, adjugate_fin_two]

private lemma conjugate_mass (s : Sector) (z : ℂ) :
    (delta s*z)*star (delta s*z) = (d s*Complex.normSq z : ℂ) := by
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_mul]
  simp [d]

private lemma diagonal_smul (s : Sector) (c : ℂ) (X : Bond) :
    diagonalStarInverse s (c • X) = c • diagonalStarInverse s X := by
  ext i j; simp [diagonalStarInverse, mul_div_assoc]

private lemma left_step_clear (s : Sector) (hs : Regular s) (z : ℂ) (hz : z ≠ 0)
    (X : Bond) : leftStep s z X = (Gamma s*Complex.normSq z : ℂ) • inverseDualTransfer s z X := by
  unfold leftStep
  rw [weights_star_clear s hs, adjugate_inverse s hs z hz, conjTranspose_smul]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,diagonal_smul]
  unfold inverseDualTransfer
  congr 1
  simp only [Gamma,Complex.ofReal_mul]
  linear_combination (schurMass s : ℂ) * conjugate_mass s z

private lemma right_step_clear (s : Sector) (hs : Regular s) (z : ℂ) (hz : z ≠ 0)
    (X : Bond) : rightStep s z X = (Gamma s*Complex.normSq z : ℂ) • inverseTransfer s z X := by
  unfold rightStep
  have hw : W s ⊙ X = (schurMass s : ℂ) • diagonalInverse s X := weights_clear s hs X
  rw [hw, adjugate_inverse s hs z hz, conjTranspose_smul]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  unfold inverseTransfer
  congr 1
  simp only [Gamma,Complex.ofReal_mul]
  linear_combination (schurMass s : ℂ) * conjugate_mass s z

private lemma inverse_left_smul (s : Sector) (z c : ℂ) (X : Bond) :
    inverseDualTransfer s z (c • X) = c • inverseDualTransfer s z X := by
  simp [inverseDualTransfer, mul_smul_comm, smul_mul_assoc, diagonal_smul]

private lemma inverse_right_smul (s : Sector) (z c : ℂ) (X : Bond) :
    inverseTransfer s z (c • X) = c • inverseTransfer s z X := by
  have h : diagonalInverse s (c • X) = c • diagonalInverse s X := by
    ext i j; simp [diagonalInverse, mul_div_assoc]
  simp [inverseTransfer, h, mul_smul_comm, smul_mul_assoc]

private lemma iterate_scale (F T : Bond → Bond) (c : ℂ)
    (h : ∀ X, F X = c • T X) (hT : ∀ (a : ℂ) X, T (a • X) = a • T X)
    (n : ℕ) (X : Bond) : F^[n] X = c^n • T^[n] X := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, h, hT,
        smul_smul, pow_succ']

private lemma central_clear (s : Sector) (hs : Regular s) (z : ℂ) (hz : z ≠ 0)
    (H : Bond) : J s z ^ 2 * H * (J s z ^ 2)ᴴ =
      (d s^2*Complex.normSq z^2 : ℂ) •
        ((G s z ^ 2)⁻¹ * H * ((G s z ^ 2)⁻¹)ᴴ) := by
  rw [adjugate_inverse s hs z hz, smul_pow, Matrix.inv_pow', conjTranspose_smul]
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  congr 1
  calc
    star ((delta s*z)^2)*(delta s*z)^2 = ((delta s*z)*star (delta s*z))^2 := by
      rw [star_pow]; ring
    _ = _ := by rw [conjugate_mass]; push_cast; ring

/-- Both original inverse-square factors and the native dual order are retained. -/
theorem numerator_clear (s : Sector) (hs : Regular s) (z : ℂ) (hz : z ≠ 0)
    (p q : ℕ) (P H : Bond) :
    leftNumerator s z p P = (Gamma s*Complex.normSq z : ℂ)^p • trialLeft s p P z ∧
    rightNumerator s z q H =
      ((Gamma s*Complex.normSq z : ℂ)^q * (d s^2*Complex.normSq z^2 : ℂ)) •
        trialRight s q H z := by
  constructor
  · exact iterate_scale _ _ _ (left_step_clear s hs z hz) (inverse_left_smul s z) p P
  · unfold rightNumerator
    rw [iterate_scale _ _ _ (right_step_clear s hs z hz) (inverse_right_smul s z),
      central_clear s hs z hz]
    have h (n : ℕ) (c : ℂ) (X : Bond) :
        (inverseTransfer s z)^[n] (c • X) = c • (inverseTransfer s z)^[n] X := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [Function.iterate_succ_apply', ih, inverse_right_smul]
    rw [h, smul_smul]
    rfl

/-- The exact real determinant row factors for arbitrary fixed target matrices. -/
theorem determinant_clear (s : Sector) (hs : Regular s) (z : ℂ) (hz : z ≠ 0)
    (p q : ℕ) (P H : Bond) :
    (leftNumerator s z p P).det.re = cL s p z * (residual s p q P H z).re ∧
    (rightNumerator s z q H).det.re = cR s q z * (residual s p q P H z).im := by
  obtain ⟨hl, hr⟩ := numerator_clear s hs z hz p q P H
  rw [hl, hr, det_smul, det_smul]
  simp only [Fintype.card_fin, OpenBoundaryMPSInteriorRootRealization.residual, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add, one_mul]
  constructor
  · norm_cast
    simp [cL, ← pow_mul, mul_pow, Nat.mul_comm]
  · norm_cast
    simp [cR, ← pow_mul, mul_pow, pow_add, Nat.mul_comm]
    ring_nf
    simp

theorem clearance_positive (s : Sector) (hs : Regular s) (z : ℂ) (hz : z ≠ 0)
    (p q : ℕ) : 0 < cL s p z ∧ 0 < cR s q z := by
  have hd : delta s ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs.1).1).1
  have hd' : 0 < d s := Complex.normSq_pos.mpr hd
  have ha : 0 < a0 s := add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  have hb : 0 < a1 s := add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _)
  have hg : 0 < Gamma s := mul_pos hd' (mul_pos (mul_pos ha hb) hs.2)
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  constructor
  · exact mul_pos (pow_pos hg _) (pow_pos ht _)
  · exact mul_pos (mul_pos (pow_pos hg _) (pow_pos hd' _)) (pow_pos ht _)

end D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
