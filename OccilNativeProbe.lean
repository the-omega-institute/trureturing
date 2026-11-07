import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

open Polynomial Finset
noncomputable section
namespace OccilNativeProbe

def f (x : ℝ) : ℝ := x ^ 2 - x + 1/2

def B (n : ℕ) (u : ℝ → ℝ) : ℝ[X] :=
  ∑ j ∈ range (n+1), C (u ((j : ℝ) / n)) * bernsteinPolynomial ℝ n j

def admissible (u : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0:ℝ) 1, 0 < u x ∧ u x ≤ 1) ∧
  (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    ∀ t ∈ Set.Icc (0:ℝ) 1, u (t*x+(1-t)*y) ≤ t*u x+(1-t)*u y)

def maxError (u : ℝ → ℝ) (n : ℕ) (M : ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0:ℝ) 1, |(B n u).eval x-u x| ≤ M) ∧
  ∃ x ∈ Set.Icc (0:ℝ) 1, |(B n u).eval x-u x| = M

def midpointError (u : ℝ → ℝ) (n : ℕ) : ℝ :=
  |(B n u).eval (1/2)-u (1/2)|

def coeff : Fin 5 → ℝ := ![1/16, 0, -1/48, 0, 1/16]

theorem f_admissible : admissible f := by
  constructor
  · intro x hx
    constructor
    · dsimp [f]; nlinarith [sq_nonneg (x-1/2)]
    · dsimp [f]; nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  · intro x hx y hy t ht
    have h := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (x-y))
    have he : t*f x+(1-t)*f y-f (t*x+(1-t)*y) = t*(1-t)*(x-y)^2 := by
      dsimp [f]; ring
    linarith

theorem f_symmetric (x : ℝ) : f (1-x)=f x := by dsimp [f]; ring

theorem B_two : B 2 f = C (1/2) * (X^2-X) + C (1/2) := by
  norm_num [B, f, Finset.sum_range_succ, bernsteinPolynomial, Nat.choose]
  <;> ring

theorem B_four : B 4 f = C (3/4) * (X^2-X) + C (1/2) := by
  norm_num [B, f, Finset.sum_range_succ, bernsteinPolynomial, Nat.choose]
  <;> ring

theorem error_two (x : ℝ) : (B 2 f).eval x-f x = x*(1-x)/2 := by
  rw [B_two]; simp [f]; ring

theorem error_four (x : ℝ) : (B 4 f).eval x-f x = x*(1-x)/4 := by
  rw [B_four]; simp [f]; ring

theorem max_two : maxError f 2 (1/8) := by
  constructor
  · intro x hx
    rw [error_two, abs_of_nonneg (div_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (by norm_num))]
    nlinarith [sq_nonneg (x-1/2)]
  · refine ⟨1/2, by norm_num, ?_⟩
    rw [error_two]; norm_num

theorem max_four : maxError f 4 (1/16) := by
  constructor
  · intro x hx
    rw [error_four, abs_of_nonneg (div_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (by norm_num))]
    nlinarith [sq_nonneg (x-1/2)]
  · refine ⟨1/2, by norm_num, ?_⟩
    rw [error_four]; norm_num

theorem mid_two : midpointError f 2 = 1/8 := by
  unfold midpointError; rw [error_two]; norm_num

theorem mid_four : midpointError f 4 = 1/16 := by
  unfold midpointError; rw [error_four]; norm_num

theorem representation : (B 4 f-C (1/16))-(B 2 f-C (1/8)) =
    ∑ j : Fin 5, C (coeff j) * bernsteinPolynomial ℝ 4 j := by
  rw [B_four, B_two]
  norm_num [coeff, Fin.sum_univ_succ, bernsteinPolynomial, Nat.choose]
  <;> ring

theorem negative : coeff 2 < 0 := by norm_num [coeff]

theorem native_counterexample :
  admissible f ∧ (∀ x ∈ Set.Icc (0:ℝ) 1, f (1-x)=f x) ∧
  (2:ℕ)=2^1 ∧ (1:ℕ)≥1 ∧
  maxError f 2 (1/8) ∧ maxError f 4 (1/16) ∧
  midpointError f 2=1/8 ∧ midpointError f 4=1/16 ∧
  ((B 4 f-C (1/16))-(B 2 f-C (1/8)) =
    ∑ j : Fin 5, C (coeff j)*bernsteinPolynomial ℝ 4 j) ∧ coeff 2<0 := by
  exact ⟨f_admissible, fun x _ => f_symmetric x, by norm_num, by norm_num,
    max_two, max_four, mid_two, mid_four, representation, negative⟩

#print native_counterexample
#print axioms native_counterexample
#check bernsteinPolynomial.linearIndependent
end OccilNativeProbe
