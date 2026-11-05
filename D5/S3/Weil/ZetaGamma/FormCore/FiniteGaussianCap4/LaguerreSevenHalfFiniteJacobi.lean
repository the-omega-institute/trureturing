/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfFiniteJacobi
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite Gaussian infinite Jacobi energy and complete boundary payment. -/
/-
SPDX-License-Identifier: Apache-2.0
Finite-source Gaussian Jacobi development, 2026-10-26.
Finite Jacobi form and an endpoint-retaining boundary payment.
All imported supplier attribution and license notices remain applicable.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfJacobi

set_option autoImplicit false
noncomputable section
open Polynomial MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf

def jacobiR (k : ℕ) : ℝ := ((k : ℝ) + 9 / 4) * ((k : ℝ) + 1 / 2)
def jacobiL (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 7 / 4)
def jacobiD (k : ℕ) : ℝ := 6 * (k : ℝ) ^ 2 + (27 / 2 : ℝ) * k + 99 / 16
def jacobiB (k : ℕ) : ℝ := Real.sqrt
  (((k : ℝ) + 1 / 2) * ((k : ℝ) + 9 / 4) * ((k : ℝ) + 1) * ((k : ℝ) + 11 / 4))

theorem jacobiR_nonneg (k : ℕ) : 0 ≤ jacobiR k := by unfold jacobiR; positivity
theorem jacobiL_nonneg (k : ℕ) : 0 ≤ jacobiL k := by unfold jacobiL; positivity
theorem jacobiB_nonneg (k : ℕ) : 0 ≤ jacobiB k := Real.sqrt_nonneg _

theorem jacobiD_decomposition (k : ℕ) :
    jacobiD k = (2 * (k : ℝ) + 9 / 4) ^ 2 + jacobiR k + jacobiL k := by
  unfold jacobiD jacobiR jacobiL
  ring

theorem jacobiD_beta (k : ℕ) :
    jacobiD k = 6 * (k : ℝ) ^ 2 + 6 * (9 / 4 : ℝ) * k +
      (9 / 4 : ℝ) ^ 2 + (9 / 4 : ℝ) / 2 := by
  unfold jacobiD
  ring

theorem jacobi_last_paid_diagonal : jacobiD 15 - jacobiR 15 = (20661 / 16 : ℝ) := by
  norm_num [jacobiD, jacobiR]

theorem jacobiB_eq (k : ℕ) :
    jacobiB k = Real.sqrt (jacobiR k) * Real.sqrt (jacobiL (k + 1)) := by
  unfold jacobiB
  rw [← Real.sqrt_mul (jacobiR_nonneg k)]
  congr 1
  simp only [jacobiR, jacobiL, Nat.cast_add, Nat.cast_one]
  ring

theorem jacobiUpper_even (k : ℕ) : jacobiUpper (2 * k) = Real.sqrt (jacobiR k) := by
  apply (sq_eq_sq₀ (jacobiUpper_nonneg _) (Real.sqrt_nonneg _)).1
  rw [jacobiUpper_sq, Real.sq_sqrt (jacobiR_nonneg k)]
  simp only [jacobiR, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem jacobiUpper_odd (k : ℕ) : jacobiUpper (2 * k + 1) = Real.sqrt (jacobiL (k + 1)) := by
  apply (sq_eq_sq₀ (jacobiUpper_nonneg _) (Real.sqrt_nonneg _)).1
  rw [jacobiUpper_sq, Real.sq_sqrt (jacobiL_nonneg _)]
  simp only [jacobiL, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- Each edge, including 15/16, is paid by this actual real square. -/
theorem jacobi_edge_payment (k : ℕ) (u v : ℝ) :
    -(jacobiR k * u ^ 2 + jacobiL (k + 1) * v ^ 2) ≤ 2 * jacobiB k * u * v := by
  have hs := sq_nonneg (Real.sqrt (jacobiR k) * u + Real.sqrt (jacobiL (k + 1)) * v)
  rw [add_sq, mul_pow, mul_pow, Real.sq_sqrt (jacobiR_nonneg k),
    Real.sq_sqrt (jacobiL_nonneg _)] at hs
  rw [jacobiB_eq]
  nlinarith

theorem jacobi_edge_abs_payment (k : ℕ) (u v : ℝ) :
    |2 * jacobiB k * u * v| ≤ jacobiR k * u ^ 2 + jacobiL (k + 1) * v ^ 2 := by
  have h₁ := jacobi_edge_payment k u v
  have h₂ := jacobi_edge_payment k u (-v)
  rw [neg_sq] at h₂
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

private theorem pair_Xpsi_self (n : ℕ) :
    polynomialPair (physicalX (psiPolynomial n)) (physicalX (psiPolynomial n)) =
      ((n : ℝ) + 9 / 4) ^ 2 + jacobiUpper n ^ 2 +
        (if n = 0 then 0 else jacobiUpper (n - 1) ^ 2) := by
  cases n with
  | zero =>
      rw [physicalX_psi_zero]
      simp only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi]
      norm_num
      ring
  | succ n =>
      rw [physicalX_psi_succ]
      simp (disch := omega) only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi,
        Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, if_pos, if_neg,
        mul_zero, mul_one, zero_mul, sub_zero, zero_sub, Nat.add_right_cancel_iff]
      simp only [ite_true, mul_one, one_mul]
      ring

theorem pair_Xeven_self (k : ℕ) :
    polynomialPair (physicalX (psiPolynomial (2 * k)))
      (physicalX (psiPolynomial (2 * k))) = jacobiD k := by
  rw [pair_Xpsi_self, jacobiUpper_even, Real.sq_sqrt (jacobiR_nonneg k),
    jacobiD_decomposition]
  cases k with
  | zero => simp [jacobiL]
  | succ k =>
      have he : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [if_neg (by omega), he, jacobiUpper_odd, Real.sq_sqrt (jacobiL_nonneg _)]
      push_cast
      ring

private theorem pair_Xpsi_next_two (n : ℕ) :
    polynomialPair (physicalX (psiPolynomial n)) (physicalX (psiPolynomial (n + 2))) =
      jacobiUpper n * jacobiUpper (n + 1) := by
  cases n with
  | zero =>
      change polynomialPair (physicalX (psiPolynomial 0))
        (physicalX (psiPolynomial (1 + 1))) = jacobiUpper 0 * jacobiUpper 1
      rw [physicalX_psi_zero, physicalX_psi_succ]
      simp (disch := omega) only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi,
        if_pos, if_neg, ite_true, ite_false, mul_zero, zero_mul, mul_one, one_mul,
        sub_zero, zero_sub, add_zero, zero_add] <;> ring
  | succ n =>
      rw [physicalX_psi_succ, show n + 1 + 2 = (n + 2) + 1 by omega, physicalX_psi_succ]
      simp (disch := omega) only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi,
        if_pos, if_neg, ite_true, ite_false, mul_zero, zero_mul, mul_one, one_mul,
        sub_zero, zero_sub, add_zero, zero_add] <;> ring

theorem pair_Xeven_next (k : ℕ) :
    polynomialPair (physicalX (psiPolynomial (2 * k)))
      (physicalX (psiPolynomial (2 * (k + 1)))) = jacobiB k := by
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pair_Xpsi_next_two,
    jacobiUpper_even, jacobiUpper_odd, ← jacobiB_eq]

private theorem pair_Xpsi_far (n m : ℕ) (h : n + 2 < m) :
    polynomialPair (physicalX (psiPolynomial n)) (physicalX (psiPolynomial m)) = 0 := by
  cases n with
  | zero =>
      cases m with
      | zero => omega
      | succ m =>
          rw [physicalX_psi_zero, physicalX_psi_succ]
          simp (disch := omega) only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi,
        if_pos, if_neg, ite_true, ite_false, mul_zero, zero_mul, mul_one, one_mul,
        sub_zero, zero_sub, add_zero, zero_add] <;> ring
  | succ n =>
      cases m with
      | zero => omega
      | succ m =>
          rw [physicalX_psi_succ, physicalX_psi_succ]
          simp (disch := omega) only [polynomialPair_sub_left, polynomialPair_sub_right,
        polynomialPair_C_left, polynomialPair_C_right, polynomialPair_psi,
        if_pos, if_neg, ite_true, ite_false, mul_zero, zero_mul, mul_one, one_mul,
        sub_zero, zero_sub, add_zero, zero_add] <;> ring

theorem pair_Xeven_far (k j : ℕ) (h : k + 1 < j) :
    polynomialPair (physicalX (psiPolynomial (2 * k)))
      (physicalX (psiPolynomial (2 * j))) = 0 :=
  pair_Xpsi_far _ _ (by omega)

def evenPolynomial (d : ℕ → ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range N, C (d k) * psiPolynomial (2 * k)

def evenJacobiEnergy (d : ℕ → ℝ) (N : ℕ) : ℝ :=
  polynomialPair (physicalX (evenPolynomial d N)) (physicalX (evenPolynomial d N))

theorem physical_evenPolynomial (d : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    physicalPolynomial (evenPolynomial d N) x =
      ∑ k ∈ Finset.range N, d k * centralPsi x (2 * k) := by
  simp only [evenPolynomial, physicalPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Finset.mul_sum, psiPolynomial, centralPsi, phi]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem evenJacobiEnergy_integral (d : ℕ → ℝ) (N : ℕ) :
    evenJacobiEnergy d N = ∫ x in Ioi (0 : ℝ), x ^ (11 / 2 : ℝ) *
      physicalPolynomial (evenPolynomial d N) x ^ 2 := by
  rw [evenJacobiEnergy, ← integral_physical_product]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [physicalPolynomial_X]
  have hxpow : x ^ (11 / 2 : ℝ) = x ^ (7 / 2 : ℝ) * x ^ 2 := by
    rw [show (11 / 2 : ℝ) = 7 / 2 + 2 by ring, Real.rpow_add hx, Real.rpow_two]
  rw [hxpow]
  ring

@[simp] theorem physicalX_add (p q : ℝ[X]) : physicalX (p + q) = physicalX p + physicalX q := by
  simp only [physicalX, mul_add]

@[simp] theorem physicalX_C (a : ℝ) (p : ℝ[X]) : physicalX (C a * p) = C a * physicalX p := by
  simp only [physicalX]
  ring

theorem physicalX_evenPolynomial (d : ℕ → ℝ) (N : ℕ) :
    physicalX (evenPolynomial d N) =
      ∑ k ∈ Finset.range N, C (d k) * physicalX (psiPolynomial (2 * k)) := by
  simp only [evenPolynomial, physicalX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem pair_evenPolynomial_next (d : ℕ → ℝ) (N : ℕ) :
    polynomialPair (physicalX (evenPolynomial d (N + 1)))
      (physicalX (psiPolynomial (2 * (N + 1)))) = jacobiB N * d N := by
  rw [physicalX_evenPolynomial, polynomialPair_sum_left, Finset.sum_range_succ]
  have hz : (∑ k ∈ Finset.range N, polynomialPair
      (C (d k) * physicalX (psiPolynomial (2 * k)))
      (physicalX (psiPolynomial (2 * (N + 1))))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [polynomialPair_C_left, pair_Xeven_far k (N + 1) (by simpa using hk), mul_zero]
  rw [hz, polynomialPair_C_left, pair_Xeven_next]
  ring

theorem evenJacobiEnergy_step (d : ℕ → ℝ) (N : ℕ) :
    evenJacobiEnergy d (N + 2) = evenJacobiEnergy d (N + 1) +
      jacobiD (N + 1) * d (N + 1) ^ 2 + 2 * jacobiB N * d N * d (N + 1) := by
  have hp : evenPolynomial d (N + 2) = evenPolynomial d (N + 1) +
      C (d (N + 1)) * psiPolynomial (2 * (N + 1)) := by
    exact Finset.sum_range_succ _ (N + 1)
  unfold evenJacobiEnergy
  rw [hp, physicalX_add, physicalX_C]
  simp only [polynomialPair_add_left, polynomialPair_add_right,
    polynomialPair_C_left, polynomialPair_C_right]
  rw [pair_Xeven_self, pair_evenPolynomial_next,
    polynomialPair_comm (physicalX (psiPolynomial (2 * (N + 1)))), pair_evenPolynomial_next]
  ring

/-- Exact finite form, including the entire last diagonal. -/
theorem evenJacobiEnergy_finite (d : ℕ → ℝ) (N : ℕ) :
    evenJacobiEnergy d N = (∑ k ∈ Finset.range N, jacobiD k * d k ^ 2) +
      2 * ∑ k ∈ Finset.range (N - 1), jacobiB k * d k * d (k + 1) := by
  induction N with
  | zero => simp [evenJacobiEnergy, evenPolynomial, physicalX, polynomialPair]
  | succ N ih =>
      cases N with
      | zero =>
          simp only [evenJacobiEnergy, evenPolynomial, Finset.sum_range_one,
            physicalX_C, polynomialPair_C_left, polynomialPair_C_right, pair_Xeven_self]
          simp
          have hzero : polynomialPair (physicalX (psiPolynomial 0))
              (physicalX (psiPolynomial 0)) = jacobiD 0 := pair_Xeven_self 0
          rw [hzero]
          ring
      | succ N =>
          rw [show N + 1 + 1 = N + 2 by omega, evenJacobiEnergy_step, ih]
          simp only [Finset.sum_range_succ, Nat.add_sub_cancel, Nat.succ_sub_one]
          ring

/-- Exactly the finite B0 head: diagonals 0..14, D15-r15, edges 0..14. -/
def jacobiPaidHead (d : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range 16, jacobiD k * d k ^ 2) +
    2 * (∑ k ∈ Finset.range 15, jacobiB k * d k * d (k + 1)) - jacobiR 15 * d 15 ^ 2

theorem jacobiPaidHead_last_diagonal (d : ℕ → ℝ) :
    jacobiPaidHead d = (∑ k ∈ Finset.range 15, jacobiD k * d k ^ 2) +
      (jacobiD 15 - jacobiR 15) * d 15 ^ 2 +
      2 * (∑ k ∈ Finset.range 15, jacobiB k * d k * d (k + 1)) := by
  rw [jacobiPaidHead, show 16 = 15 + 1 from rfl, Finset.sum_range_succ]
  ring

/-- Endpoint retained. The first inductive payment is the edge k=15 itself. -/
theorem jacobi_paid_prefix_with_endpoint (d : ℕ → ℝ) (m : ℕ) :
    jacobiPaidHead d + (∑ i ∈ Finset.range m,
      (2 * (16 + i : ℕ) + 9 / 4 : ℝ) ^ 2 * d (16 + i) ^ 2) +
      jacobiR (15 + m) * d (15 + m) ^ 2 ≤ evenJacobiEnergy d (16 + m) := by
  induction m with
  | zero =>
      rw [Nat.add_zero, Nat.add_zero, Finset.sum_range_zero, evenJacobiEnergy_finite]
      simp only [Nat.reduceSub, jacobiPaidHead]
      linarith
  | succ m ih =>
      have hp := jacobi_edge_payment (15 + m) (d (15 + m)) (d (16 + m))
      have hD := jacobiD_decomposition (16 + m)
      have he : evenJacobiEnergy d (16 + (m + 1)) =
          evenJacobiEnergy d (16 + m) + jacobiD (16 + m) * d (16 + m) ^ 2 +
            2 * jacobiB (15 + m) * d (15 + m) * d (16 + m) := by
        have hn₁ : (15 + m) + 1 = 16 + m := by omega
        have hn₂ : (15 + m) + 2 = 16 + (m + 1) := by omega
        simpa only [hn₁, hn₂] using evenJacobiEnergy_step d (15 + m)
      rw [he, Finset.sum_range_succ]
      have hn : 15 + m + 1 = 16 + m := by omega
      rw [hn] at hp
      have hn' : 15 + (m + 1) = 16 + m := by omega
      rw [hn']
      push_cast at hD ih ⊢
      have hDd := congrArg (fun t : ℝ => t * d (16 + m) ^ 2) hD
      nlinarith [hDd]

end FiniteGaussianCap4.LaguerreSevenHalf
