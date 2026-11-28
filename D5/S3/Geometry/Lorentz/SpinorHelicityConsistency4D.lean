/- GID: D5/S3/Geometry/Lorentz/SpinorHelicityConsistency4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/SpinorHelicityConsistency4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spinor brackets and degree-independent four-point polynomial consistency. -/

import OmegaBuild.Commands
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-! Spinor brackets and polynomial restrictions on the three four-point channel lines. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.SpinorHelicityConsistency4D

open Matrix Polynomial
open scoped Matrix BigOperators

abbrev Spinor (K : Type*) := Fin 2 → K

variable {K : Type*} [Field K]

/-- The alternating spinor bracket, for either chirality. -/
def angle (u v : Spinor K) : K := u 0 * v 1 - u 1 * v 0

theorem angle_antisymm (u v : Spinor K) : angle u v = -angle v u := by
  unfold angle
  ring

theorem angle_self (u : Spinor K) : angle u u = 0 := by
  unfold angle
  ring

theorem angle_det_covariance (A : Matrix (Fin 2) (Fin 2) K) (u v : Spinor K) :
    angle (A *ᵥ u) (A *ᵥ v) = A.det * angle u v := by
  simp [angle, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem schouten_identity (u v w z : Spinor K) :
    angle u v * angle w z + angle u w * angle z v + angle u z * angle v w = 0 := by
  unfold angle
  ring

theorem spinor_frame_transport (u v w x y z : Spinor K)
    (hn : angle u v ≠ 0) (h₁ : angle u v = angle x y)
    (h₂ : angle u w = angle x z) (h₃ : angle v w = angle y z) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 ∧
      A *ᵥ u = x ∧ A *ᵥ v = y ∧ A *ᵥ w = z := by
  have expand (a b c : Spinor K) (hd : angle a b ≠ 0) :
      c = (-angle b c / angle a b) • a + (angle a c / angle a b) • b := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    fin_cases i
    · have h := schouten_identity a b c (![0, 1] : Spinor K)
      simp [angle] at h
      unfold angle
      simp only [Fin.zero_eta]
      linear_combination h
    · have h := schouten_identity a b c (![1, 0] : Spinor K)
      simp [angle] at h
      unfold angle
      simp only [Fin.mk_one]
      linear_combination -h
  let A : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j =>
    if j = 0 then (x i * v 1 - y i * u 1) / angle u v
    else (y i * u 0 - x i * v 0) / angle u v
  have hu : A *ᵥ u = x := by
    ext i
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    unfold angle
    ring
  have hv : A *ᵥ v = y := by
    ext i
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp
    unfold angle
    ring
  have hd := angle_det_covariance A u v
  rw [hu, hv, ← h₁] at hd
  have detA : A.det = 1 := by
    apply mul_right_cancel₀ hn
    simpa only [one_mul] using hd.symm
  refine ⟨A, detA, hu, hv, ?_⟩
  rw [expand u v w hn, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    hu, hv, h₁, h₂, h₃]
  exact (expand x y z (h₁ ▸ hn)).symm

/-- The outer product of the two chiral spinors. -/
def bispinor (l lt : Spinor K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => l i * lt j

theorem bispinor_det (l lt : Spinor K) : (bispinor l lt).det = 0 := by
  simp [bispinor, Matrix.det_fin_two]
  ring

theorem mandelstam_det (l₁ lt₁ l₂ lt₂ : Spinor K) :
    (bispinor l₁ lt₁ + bispinor l₂ lt₂).det = angle l₁ l₂ * angle lt₁ lt₂ := by
  simp [bispinor, angle, Matrix.det_fin_two]
  ring

theorem null_bispinor_factorization_iff (M : Matrix (Fin 2) (Fin 2) K) :
    M.det = 0 ↔ ∃ l lt : Spinor K, M = bispinor l lt := by
  constructor
  · intro h
    classical
    by_cases hp : ∃ i j, M i j ≠ 0
    · obtain ⟨i, j, hij⟩ := hp
      refine ⟨fun a => M a j, fun b => M i b / M i j, ?_⟩
      ext a b
      simp only [bispinor, Matrix.of_apply]
      rw [← mul_div_assoc]
      apply (eq_div_iff hij).mpr
      rw [Matrix.det_fin_two] at h
      fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one] <;>
        first | (ring; done) | (linear_combination h; done) | linear_combination -h
    · push_neg at hp
      exact ⟨0, 0, by ext i j; simp [bispinor, hp]⟩
  · rintro ⟨l, lt, rfl⟩
    exact bispinor_det l lt

private theorem three_point_of_nonzero (u v w x y z : Spinor K)
    (h : bispinor u x + bispinor v y + bispinor w z = 0) (hn : angle u v ≠ 0) :
    angle x y = 0 ∧ angle y z = 0 ∧ angle z x = 0 := by
  have h0 (j : Fin 2) : u 0 * x j + v 0 * y j + w 0 * z j = 0 := by
    simpa [bispinor] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 j) h
  have h1 (j : Fin 2) : u 1 * x j + v 1 * y j + w 1 * z j = 0 := by
    simpa [bispinor] using congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 j) h
  have hx (j : Fin 2) : angle u v * x j = angle v w * z j := by
    unfold angle
    linear_combination v 1 * h0 j - v 0 * h1 j
  have hy (j : Fin 2) : angle u v * y j = -angle u w * z j := by
    unfold angle
    linear_combination u 0 * h1 j - u 1 * h0 j
  have hx' (j : Fin 2) : x j = (angle v w / angle u v) * z j := by
    apply (mul_left_cancel₀ hn)
    rw [hx]
    field_simp
  have hy' (j : Fin 2) : y j = (-angle u w / angle u v) * z j := by
    apply (mul_left_cancel₀ hn)
    rw [hy]
    field_simp
  constructor
  · have hm : bispinor u x + bispinor v y = -bispinor w z :=
      eq_neg_of_add_eq_zero_left h
    have hd := congrArg Matrix.det hm
    rw [mandelstam_det, Matrix.det_neg, bispinor_det, mul_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left hn
  constructor
  · unfold angle
    rw [hy' 0, hy' 1]
    ring
  · unfold angle
    rw [hx' 0, hx' 1]
    ring

theorem three_point_kinematics_dichotomy (l₁ l₂ l₃ lt₁ lt₂ lt₃ : Spinor K)
    (h : bispinor l₁ lt₁ + bispinor l₂ lt₂ + bispinor l₃ lt₃ = 0) :
    (angle l₁ l₂ = 0 ∧ angle l₂ l₃ = 0 ∧ angle l₃ l₁ = 0) ∨
    (angle lt₁ lt₂ = 0 ∧ angle lt₂ lt₃ = 0 ∧ angle lt₃ lt₁ = 0) := by
  by_cases h12 : angle l₁ l₂ = 0
  · by_cases h23 : angle l₂ l₃ = 0
    · by_cases h31 : angle l₃ l₁ = 0
      · exact Or.inl ⟨h12, h23, h31⟩
      · obtain ⟨a,b,c⟩ := three_point_of_nonzero l₃ l₁ l₂ lt₃ lt₁ lt₂
          (by simpa only [add_assoc, add_comm, add_left_comm] using h) h31
        exact Or.inr ⟨b,c,a⟩
    · obtain ⟨a,b,c⟩ := three_point_of_nonzero l₂ l₃ l₁ lt₂ lt₃ lt₁
        (by simpa only [add_assoc, add_comm, add_left_comm] using h) h23
      exact Or.inr ⟨c,a,b⟩
  · exact Or.inr (three_point_of_nonzero l₁ l₂ l₃ lt₁ lt₂ lt₃ h h12)

theorem three_point_real_brackets_vanish (l₁ l₂ l₃ : Spinor ℂ)
    (h : bispinor l₁ (star l₁) + bispinor l₂ (star l₂) + bispinor l₃ (star l₃) = 0) :
    (angle l₁ l₂ = 0 ∧ angle l₂ l₃ = 0 ∧ angle l₃ l₁ = 0) ∧
    (angle (star l₁) (star l₂) = 0 ∧ angle (star l₂) (star l₃) = 0 ∧
      angle (star l₃) (star l₁) = 0) := by
  have hs (u v : Spinor ℂ) : angle (star u) (star v) = star (angle u v) := by
    simp [angle, star_sub, star_mul, mul_comm]
  rcases three_point_kinematics_dichotomy l₁ l₂ l₃ (star l₁) (star l₂) (star l₃) h with h' | h'
  · exact ⟨h', by simp [hs, h'.1, h'.2.1, h'.2.2]⟩
  · exact ⟨by simpa [hs] using h', h'⟩

theorem three_point_scaled_conjugate_brackets_vanish (l₁ l₂ l₃ : Spinor ℂ)
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : bispinor l₁ (a • star l₁) + bispinor l₂ (b • star l₂) +
      bispinor l₃ (c • star l₃) = 0) :
    (angle l₁ l₂ = 0 ∧ angle l₂ l₃ = 0 ∧ angle l₃ l₁ = 0) ∧
    (angle (a • star l₁) (b • star l₂) = 0 ∧ angle (b • star l₂) (c • star l₃) = 0 ∧
      angle (c • star l₃) (a • star l₁) = 0) := by
  have scale (u v : Spinor ℂ) (x y : ℂ) :
      angle (x • star u) (y • star v) = (x * y) * star (angle u v) := by
    simp [angle, star_sub, star_mul, Pi.smul_apply, smul_eq_mul]
    ring
  rcases three_point_kinematics_dichotomy l₁ l₂ l₃ (a • star l₁) (b • star l₂)
      (c • star l₃) h with hh | hh
  · exact ⟨hh, by simp [scale, hh.1, hh.2.1, hh.2.2]⟩
  · refine ⟨?_, hh⟩
    simpa [scale, ha, hb, hc] using hh

theorem three_point_little_group_exponents_unique (h₁ h₂ h₃ d₁ d₂ d₃ : ℤ) :
    (d₂ + d₃ = -2 * h₁ ∧ d₃ + d₁ = -2 * h₂ ∧ d₁ + d₂ = -2 * h₃) ↔
    (d₁ = h₁ - h₂ - h₃ ∧ d₂ = h₂ - h₃ - h₁ ∧ d₃ = h₃ - h₁ - h₂) := by
  omega

/-- The determinant of the sum of two rank-one momenta. -/
def mandelstam (l lt : Fin 4 → Spinor K) (i j : Fin 4) : K :=
  angle (l i) (l j) * angle (lt i) (lt j)

/-- The helicity prefactor for negative helicity on particles 1 and 3. -/
def helicityPrefactor (l lt : Fin 4 → Spinor K) : K :=
  angle (l 0) (l 2) ^ 2 * angle (lt 1) (lt 3) ^ 2

private theorem four_point_contraction (l lt : Fin 4 → Spinor K)
    (h : ∑ i, bispinor (l i) (lt i) = 0) (i j : Fin 4) :
    ∑ k, angle (l i) (l k) * angle (lt k) (lt j) = 0 := by
  have hm (a b : Fin 2) : ∑ k, l k a * lt k b = 0 := by
    simpa [bispinor, Matrix.sum_apply] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M a b) h
  simp only [angle, Fin.sum_univ_four] at hm ⊢
  linear_combination
    l i 0 * lt j 1 * hm 1 0 - l i 0 * lt j 0 * hm 1 1 -
    l i 1 * lt j 1 * hm 0 0 + l i 1 * lt j 0 * hm 0 1

theorem four_point_parke_taylor_polynomial (l lt : Fin 4 → Spinor K)
    (h : ∑ i, bispinor (l i) (lt i) = 0) :
    helicityPrefactor l lt *
      (angle (l 0) (l 1) * angle (l 1) (l 2) * angle (l 2) (l 3) * angle (l 3) (l 0)) =
      -(angle (l 0) (l 2) ^ 4 * (mandelstam l lt 0 1 * mandelstam l lt 0 3)) := by
  have h₁ := four_point_contraction l lt h 2 1
  have h₃ := four_point_contraction l lt h 2 3
  simp only [Fin.sum_univ_four, angle_self, zero_mul, mul_zero, add_zero, zero_add] at h₁ h₃
  rw [angle_antisymm (l 2) (l 0), angle_antisymm (lt 3) (lt 1)] at h₁
  rw [angle_antisymm (l 2) (l 0), angle_antisymm (l 2) (l 1)] at h₃
  have e₁ : angle (l 0) (l 2) * angle (lt 0) (lt 1) =
      -(angle (l 2) (l 3) * angle (lt 1) (lt 3)) := by linear_combination -h₁
  have e₃ : angle (l 0) (l 2) * angle (lt 0) (lt 3) =
      -(angle (l 1) (l 2) * angle (lt 1) (lt 3)) := by linear_combination -h₃
  unfold helicityPrefactor mandelstam
  rw [angle_antisymm (l 3) (l 0)]
  calc
    _ = -(angle (l 0) (l 2) ^ 2 * angle (l 0) (l 1) * angle (l 0) (l 3) *
      (angle (l 2) (l 3) * angle (lt 1) (lt 3)) *
      (angle (l 1) (l 2) * angle (lt 1) (lt 3))) := by ring
    _ = _ := by rw [← neg_eq_iff_eq_neg.mpr e₁, ← neg_eq_iff_eq_neg.mpr e₃]; ring

theorem four_point_parke_taylor_mandelstam_identity (l lt : Fin 4 → Spinor K)
    (h : ∑ i, bispinor (l i) (lt i) = 0)
    (hs : mandelstam l lt 0 1 * mandelstam l lt 0 3 ≠ 0)
    (hb : angle (l 0) (l 1) * angle (l 1) (l 2) * angle (l 2) (l 3) *
      angle (l 3) (l 0) ≠ 0) :
    helicityPrefactor l lt / (mandelstam l lt 0 1 * mandelstam l lt 0 3) =
      -(angle (l 0) (l 2) ^ 4 /
        (angle (l 0) (l 1) * angle (l 1) (l 2) * angle (l 2) (l 3) * angle (l 3) (l 0))) := by
  rw [← neg_div]
  exact (div_eq_div_iff hs hb).mpr (by
    simpa only [neg_mul] using four_point_parke_taylor_polynomial l lt h)

theorem four_point_klt_identity (k s t u : K) :
    (-s) * (k / (s * t)) * (k / (s * u)) = -(k ^ 2) / (s * t * u) := by
  by_cases hs : s = 0
  · simp [hs]
  by_cases ht : t = 0
  · simp [ht]
  by_cases hu : u = 0
  · simp [hu]
  field_simp

theorem four_point_klt_parke_taylor (l lt : Fin 4 → Spinor K)
    (h : ∑ i, bispinor (l i) (lt i) = 0)
    (hs : mandelstam l lt 0 1 * mandelstam l lt 0 3 ≠ 0)
    (ht : mandelstam l lt 0 1 * mandelstam l lt 0 2 ≠ 0)
    (hb : angle (l 0) (l 1) * angle (l 1) (l 2) * angle (l 2) (l 3) *
      angle (l 3) (l 0) ≠ 0)
    (hc : angle (l 0) (l 1) * angle (l 1) (l 3) * angle (l 3) (l 2) *
      angle (l 2) (l 0) ≠ 0) :
    (-mandelstam l lt 0 1) *
      (angle (l 0) (l 2) ^ 4 /
        (angle (l 0) (l 1) * angle (l 1) (l 2) * angle (l 2) (l 3) * angle (l 3) (l 0))) *
      (angle (l 0) (l 2) ^ 4 /
        (angle (l 0) (l 1) * angle (l 1) (l 3) * angle (l 3) (l 2) * angle (l 2) (l 0))) =
      -(helicityPrefactor l lt ^ 2) /
        (mandelstam l lt 0 1 * mandelstam l lt 0 3 * mandelstam l lt 0 2) := by
  have hp : bispinor (l 0) (lt 0) + bispinor (l 2) (lt 2) =
      -(bispinor (l 1) (lt 1) + bispinor (l 3) (lt 3)) := by
    simp only [Fin.sum_univ_four] at h
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc, add_comm, add_left_comm] using h
  have hd := congrArg Matrix.det hp
  rw [mandelstam_det, Matrix.det_neg, mandelstam_det] at hd
  have hcomp : mandelstam l lt 0 2 = mandelstam l lt 1 3 := by
    simpa [mandelstam] using hd
  have h₁ := four_point_contraction l lt h 2 1
  simp only [Fin.sum_univ_four, angle_self, zero_mul, mul_zero, add_zero, zero_add] at h₁
  rw [angle_antisymm (l 2) (l 0), angle_antisymm (lt 3) (lt 1)] at h₁
  have e₁ : angle (l 2) (l 3) * angle (lt 1) (lt 3) =
      -(angle (l 0) (l 2) * angle (lt 0) (lt 1)) := by linear_combination -h₁
  have hsecond : helicityPrefactor l lt /
      (mandelstam l lt 0 1 * mandelstam l lt 0 2) =
      -(angle (l 0) (l 2) ^ 4 /
        (angle (l 0) (l 1) * angle (l 1) (l 3) * angle (l 3) (l 2) * angle (l 2) (l 0))) := by
    rw [← neg_div]
    apply (div_eq_div_iff ht hc).mpr
    rw [hcomp]
    unfold helicityPrefactor mandelstam
    rw [angle_antisymm (l 3) (l 2), angle_antisymm (l 2) (l 0)]
    linear_combination
      angle (l 0) (l 2) ^ 3 * angle (l 0) (l 1) * angle (l 1) (l 3) *
        angle (lt 1) (lt 3) * e₁
  have hfirst := four_point_parke_taylor_mandelstam_identity l lt h hs hb
  have hf := congrArg Neg.neg hfirst
  have hg := congrArg Neg.neg hsecond
  simp only [neg_neg] at hf hg
  rw [← hf, ← hg]
  simpa only [mul_neg, neg_mul, neg_neg] using four_point_klt_identity
    (helicityPrefactor l lt) (mandelstam l lt 0 1) (mandelstam l lt 0 3) (mandelstam l lt 0 2)

/-- Restriction to the s-channel line. -/
def eval_s0 : MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![0, Polynomial.X]

/-- Restriction to the t-channel line. -/
def eval_t0 : MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0]

/-- Restriction to the u-channel line, where t = -s. -/
def eval_u0 : MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, -Polynomial.X]

private theorem channel_coefficients (P : MvPolynomial (Fin 2) K) :
    (eval_s0 P).coeff 0 = (eval_t0 P).coeff 0 ∧
    (eval_t0 P).coeff 0 = (eval_u0 P).coeff 0 ∧
    (eval_u0 P).coeff 1 = (eval_t0 P).coeff 1 - (eval_s0 P).coeff 1 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [eval_s0, eval_t0, eval_u0, MvPolynomial.eval₂Hom_C]
  | add P Q hP hQ =>
    simp only [map_add, Polynomial.coeff_add]
    exact ⟨by rw [hP.1, hQ.1], by rw [hP.2.1, hQ.2.1], by rw [hP.2.2, hQ.2.2]; ring⟩
  | mul_X P i hP =>
    fin_cases i <;>
      simp [map_mul, eval_s0, eval_t0, eval_u0, MvPolynomial.eval₂Hom_X',
        Polynomial.coeff_mul_X, Polynomial.mul_coeff_zero, mul_neg] at *
    · exact hP.2.1.symm
    · rw [hP.1, hP.2.1]

theorem spin_one_four_point_consistency_iff (c_s c_t c_u : K) :
    (∃ P : MvPolynomial (Fin 2) K,
      eval_s0 P = Polynomial.C c_s * Polynomial.X ∧
      eval_t0 P = Polynomial.C (-c_t) * Polynomial.X ∧
      eval_u0 P = Polynomial.C c_u * Polynomial.X) ↔ c_s + c_t + c_u = 0 := by
  constructor
  · rintro ⟨P, hs, ht, hu⟩
    have h := (channel_coefficients P).2.2
    rw [hs, ht, hu] at h
    simp at h
    linear_combination h
  · intro h
    have hc : -c_t - c_s = c_u := by linear_combination -h
    refine ⟨MvPolynomial.C (-c_t) * MvPolynomial.X 0 + MvPolynomial.C c_s * MvPolynomial.X 1,
      ?_, ?_, ?_⟩
    · simp only [map_add, map_mul, eval_s0, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add]
    · simp only [map_add, map_mul, eval_t0, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
    · simp only [map_add, map_mul, eval_u0, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_neg, ← sub_eq_add_neg, ← sub_mul, ← map_sub, hc]

theorem spin_two_four_point_consistency_iff (c_s c_t c_u : K) :
    (∃ P : MvPolynomial (Fin 2) K,
      eval_s0 P = Polynomial.C c_s ∧ eval_t0 P = Polynomial.C c_t ∧
      eval_u0 P = Polynomial.C c_u) ↔ c_s = c_t ∧ c_t = c_u := by
  constructor
  · rintro ⟨P, hs, ht, hu⟩
    have h := channel_coefficients P
    rw [hs, ht, hu] at h
    simpa using h
  · rintro ⟨rfl, rfl⟩
    exact ⟨MvPolynomial.C c_s, by simp [eval_s0], by simp [eval_t0], by simp [eval_u0]⟩

theorem equivalence_principle_from_consistency (κg κa : K) :
    (∃ P : MvPolynomial (Fin 2) K,
      eval_s0 P = Polynomial.C (κg * κa) ∧ eval_t0 P = Polynomial.C (κa ^ 2) ∧
      eval_u0 P = Polynomial.C (κa ^ 2)) ↔ κa = 0 ∨ κa = κg := by
  rw [spin_two_four_point_consistency_iff]
  constructor
  · rintro ⟨h, _⟩
    have hp : κa * (κa - κg) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hp with h₀ | h₁
    · exact Or.inl h₀
    · exact Or.inr (sub_eq_zero.mp h₁)
  · rintro (rfl | rfl) <;> simp [pow_two]

theorem higher_spin_four_point_exclusion_iff (s : ℕ) (hs : 3 ≤ s) (c_s c_t c_u : K) :
    (∃ P : MvPolynomial (Fin 2) K,
      Polynomial.X ^ (s - 2) * eval_s0 P = Polynomial.C c_s ∧
      Polynomial.X ^ (s - 2) * eval_t0 P = Polynomial.C ((-1 : K) ^ s * c_t) ∧
      Polynomial.X ^ (s - 2) * eval_u0 P = Polynomial.C c_u) ↔
    c_s = 0 ∧ c_t = 0 ∧ c_u = 0 := by
  have hn : s - 2 ≠ 0 := by omega
  constructor
  · rintro ⟨P, h₁, h₂, h₃⟩
    have hc (p : Polynomial K) (c : K) (h : Polynomial.X ^ (s - 2) * p = Polynomial.C c) :
        c = 0 := by
      have hh := congrArg (fun p : Polynomial K => p.coeff 0) h
      simpa [Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, hn, Ne.symm hn] using hh.symm
    exact ⟨hc _ _ h₁, (mul_eq_zero.mp (hc _ _ h₂)).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)),
      hc _ _ h₃⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨0, by simp, by simp, by simp⟩

section Color

variable {ι : Type*} [Fintype ι]

/-- The contracted Jacobi equation obtained from the three color factors. -/
theorem spin_one_jacobi_from_consistency (f : ι → ι → ι → K)
    (hf : ∀ a b e, f a b e = -f b a e)
    (hf₂ : ∀ a b e, f a b e = -f a e b) (a b c d : ι)
    (h : ∃ P : MvPolynomial (Fin 2) K,
      eval_s0 P = Polynomial.C (∑ e, f a b e * f c d e) * Polynomial.X ∧
      eval_t0 P = Polynomial.C (-(∑ e, f a d e * f b c e)) * Polynomial.X ∧
      eval_u0 P = Polynomial.C (∑ e, f a c e * f d b e) * Polynomial.X) :
    ∑ e, (f a b e * f e c d + f b c e * f e a d + f c a e * f e b d) = 0 := by
  have hh := spin_one_four_point_consistency_iff _ _ _ |>.mp h
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib] at hh
  calc
    _ = ∑ e, (f a b e * f c d e + f a d e * f b c e + f a c e * f d b e) := by
      apply Finset.sum_congr rfl
      intro e _
      have cyc (i j : ι) : f e i j = f i j e := by
        rw [hf e i j, hf₂ i e j, neg_neg]
      rw [cyc c d, cyc a d, cyc b d, hf c a e, hf d b e]
      ring
    _ = 0 := hh

/-- The coupling matrix for the external species a. -/
def couplingMatrix (κ : ι → ι → ι → K) (a : ι) : Matrix ι ι K :=
  Matrix.of fun b c => κ a b c

theorem multi_graviton_commutativity_and_decoupling (κ : ι → ι → ι → K)
    (h₁ : ∀ a b c, κ a b c = κ b a c) (h₂ : ∀ a b c, κ a b c = κ a c b) :
    (∀ a b c d,
      (∑ e, κ a b e * κ c d e) = ∑ e, κ a d e * κ b c e ∧
      (∑ e, κ a d e * κ b c e) = ∑ e, κ a c e * κ d b e) ↔
    (∀ a b, couplingMatrix κ a * couplingMatrix κ b = couplingMatrix κ b * couplingMatrix κ a ∧
      couplingMatrix κ a * couplingMatrix κ b = ∑ e, κ a b e • couplingMatrix κ e) := by
  have cyc (a b c : ι) : κ a b c = κ b c a := (h₁ a b c).trans (h₂ b a c)
  have mulEntry (a b c d : ι) : (couplingMatrix κ a * couplingMatrix κ b) c d =
      ∑ e, κ a c e * κ b d e := by
    simp only [Matrix.mul_apply, couplingMatrix, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro e _
    rw [h₂ b e d]
  have sumEntry (a b c d : ι) :
      (∑ e, κ a b e • couplingMatrix κ e) c d = ∑ e, κ a b e * κ c d e := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, couplingMatrix, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro e _
    rw [cyc e c d]
  constructor
  · intro h a b
    constructor <;> ext c d
    · rw [mulEntry, mulEntry]
      simpa only [h₁ b c, h₁ b d, h₁ a d, mul_comm] using (h a b c d).2.symm
    · rw [mulEntry, sumEntry]
      simpa only [h₁ d b] using ((h a b c d).1.trans (h a b c d).2).symm
  · intro h a b c d
    have ha := congrArg (fun M : Matrix ι ι K => M c d) (h a b).2
    have hb := congrArg (fun M : Matrix ι ι K => M d c) (h a b).2
    rw [mulEntry, sumEntry] at ha hb
    simp only [h₁ d c] at hb
    exact ⟨hb.symm, by simpa only [h₁ d b] using hb.trans ha.symm⟩

/-- The product determined by the symmetric cubic coupling tensor. -/
def gravitonProduct (κ : ι → ι → ι → K) (x y : ι → K) : ι → K :=
  fun c => ∑ a, x a * (couplingMatrix κ a *ᵥ y) c

/-- Independent common eigenvectors cannot interact through the cubic coupling. -/
theorem graviton_cross_product_zero (κ : ι → ι → ι → K)
    (h₁ : ∀ a b c, κ a b c = κ b a c) (h₂ : ∀ a b c, κ a b c = κ a c b)
    (x y : ι → K) (χ ψ : ι → K)
    (hx : ∀ a, couplingMatrix κ a *ᵥ x = χ a • x)
    (hy : ∀ a, couplingMatrix κ a *ᵥ y = ψ a • y)
    (hli : LinearIndependent K ![x, y]) : gravitonProduct κ x y = 0 := by
  have comm : gravitonProduct κ x y = gravitonProduct κ y x := by
    funext c
    simp only [gravitonProduct, Matrix.mulVec, dotProduct, couplingMatrix, Matrix.of_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [h₂ b c a, h₁ b a c, h₂ a b c]
    ring
  have eigen (u v : ι → K) (eig : ι → K)
      (hv : ∀ a, couplingMatrix κ a *ᵥ v = eig a • v) :
      gravitonProduct κ u v = (∑ a, u a * eig a) • v := by
    funext c
    simp only [gravitonProduct, hv, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have he := (eigen y x χ hx).symm.trans (comm.symm.trans (eigen x y ψ hy))
  rw [eigen x y ψ hy, (LinearIndependent.eq_zero_of_pair' hli he).2, zero_smul]

/-- The joint eigenspaces of the real coupling matrices exhaust species space. -/
theorem multi_graviton_joint_eigenspaces [DecidableEq ι] (κ : ι → ι → ι → ℝ)
    (h₁ : ∀ a b c, κ a b c = κ b a c) (h₂ : ∀ a b c, κ a b c = κ a c b)
    (h : ∀ a b c d,
      (∑ e, κ a b e * κ c d e) = ∑ e, κ a d e * κ b c e ∧
      (∑ e, κ a d e * κ b c e) = ∑ e, κ a c e * κ d b e) :
    (⨆ χ : ι → ℝ, ⨅ a,
      Module.End.eigenspace (couplingMatrix κ a).toEuclideanLin (χ a)) = ⊤ := by
  classical
  apply LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
  · intro a
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    apply Matrix.isHermitian_iff_isSymm.mpr
    exact Matrix.IsSymm.ext fun i j => h₂ a j i
  · intro a b _
    change Commute (Matrix.toLpLinAlgEquiv 2 (couplingMatrix κ a))
      (Matrix.toLpLinAlgEquiv 2 (couplingMatrix κ b))
    exact (show Commute (couplingMatrix κ a) (couplingMatrix κ b) from
      ((multi_graviton_commutativity_and_decoupling κ h₁ h₂).mp h a b).1).map
        (Matrix.toLpLinAlgEquiv 2)

/-- A common eigenbasis with no cross-species cubic products. -/
theorem multi_graviton_decoupled_basis (κ : ι → ι → ι → ℝ)
    (h₁ : ∀ a b c, κ a b c = κ b a c) (h₂ : ∀ a b c, κ a b c = κ a c b)
    (h : ∀ a b c d,
      (∑ e, κ a b e * κ c d e) = ∑ e, κ a d e * κ b c e ∧
      (∑ e, κ a d e * κ b c e) = ∑ e, κ a c e * κ d b e) :
    ∃ b : Module.Basis ι ℝ (ι → ℝ),
      (∀ i, ∃ χ : ι → ℝ, ∀ a, couplingMatrix κ a *ᵥ b i = χ a • b i) ∧
      (∀ i j, i ≠ j → gravitonProduct κ (b i) (b j) = 0) := by
  classical
  let S : Set (EuclideanSpace ℝ ι) := {v | ∃ χ : ι → ℝ,
    ∀ a, v ∈ Module.End.eigenspace (couplingMatrix κ a).toEuclideanLin (χ a)}
  have hspan : ⊤ ≤ Submodule.span ℝ S := by
    rw [← multi_graviton_joint_eigenspaces κ h₁ h₂ h]
    apply iSup_le
    intro χ v hv
    exact Submodule.subset_span ⟨χ, fun a => (Submodule.mem_iInf _).mp hv a⟩
  let base := Module.Basis.ofSpan hspan
  let raw := base.map (WithLp.linearEquiv 2 ℝ (ι → ℝ))
  let e := raw.indexEquiv (Pi.basisFun ℝ ι)
  let b := raw.reindex e
  have he (i : ι) : ∃ χ : ι → ℝ, ∀ a, couplingMatrix κ a *ᵥ b i = χ a • b i := by
    have hm : base (e.symm i) ∈ S :=
      Module.Basis.ofSpan_subset hspan (Set.mem_range_self _)
    obtain ⟨χ, hχ⟩ := hm
    refine ⟨χ, fun a => ?_⟩
    have hh := Module.End.mem_eigenspace_iff.mp (hχ a)
    simpa [b, raw, Module.Basis.reindex_apply, WithLp.linearEquiv] using congrArg WithLp.ofLp hh
  refine ⟨b, he, ?_⟩
  intro i j hij
  obtain ⟨χ, hχ⟩ := he i
  obtain ⟨ψ, hψ⟩ := he j
  apply graviton_cross_product_zero κ h₁ h₂ _ _ χ ψ hχ hψ
  have hinj : Function.Injective (![i, j] : Fin 2 → ι) := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hh := b.linearIndependent.comp (![i, j] : Fin 2 → ι) hinj
  convert hh using 1
  funext k
  fin_cases k <;> rfl

end Color

/-- A symmetric two-species tensor with incompatible coupling matrices. -/
theorem two_graviton_noncommuting_example :
    ∃ κ : Fin 2 → Fin 2 → Fin 2 → ℝ,
      (∀ a b c, κ a b c = κ b a c) ∧ (∀ a b c, κ a b c = κ a c b) ∧
      couplingMatrix κ 0 * couplingMatrix κ 1 ≠ couplingMatrix κ 1 * couplingMatrix κ 0 := by
  let κ : Fin 2 → Fin 2 → Fin 2 → ℝ := fun a b c =>
    if a.val + b.val + c.val = 1 then 1 else 0
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro a b c
    simp [κ, Nat.add_comm a.val b.val]
  · intro a b c
    simp [κ, Nat.add_assoc, Nat.add_comm b.val c.val]
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [κ, couplingMatrix, Matrix.mul_apply, Fin.sum_univ_two] at he


end D5.S3.Geometry.Lorentz.SpinorHelicityConsistency4D
