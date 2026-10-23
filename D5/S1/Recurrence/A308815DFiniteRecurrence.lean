/- GID: D5/S1/Recurrence/A308815DFiniteRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/A308815DFiniteRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: []
   utility: none
   digest: Mathar's D-finite recurrence for the alternating Catalan numbers. -/

/-
Public theorem result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#15713; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15923
DTR reading: DTR-Unregistered for result (Observe); no Reg mirror is delivered.
The Catalan series and its quadratic equation use pinned Mathlib directly;
no new Catalan-series alias or companion quadratic theorem is introduced.
All private theorem steps are bind-only; their consumers are:
  cat_ode -> certificate; p_coeff -> b_sum, high_p; b_sum -> a_eq;
  a_eq -> result; r_deriv -> certificate; certificate -> annihilation;
  high_p -> forcing_zero; forcing_zero -> annihilation;
  euler_coeff -> annihilation; annihilation -> b_recurrence;
  b_recurrence -> result.
The coefficient certificate is X*U' - 2*(m+3)*U; its degree-2*(m+3)
coefficient vanishes, as does the forcing polynomial's coefficient.
-/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination

open scoped BigOperators
open Finset PowerSeries
namespace D5.S1.Recurrence.A308815DFiniteRecurrence

def a308815 (n : ℕ) : ℤ :=
  16 ^ n * ∑ i ∈ Finset.range (n + 1), (-2 : ℤ) ^ i * (n.choose i : ℤ) * (catalan (2 * n - i) : ℤ)

def claim : Prop := ∀ n : ℕ, 3 ≤ n →
  (n : ℤ) * (2 * n + 1) * a308815 n -
    32 * (9 * n - 4) * (n - 1) * a308815 (n - 1) +
    1024 * (3 * n ^ 2 - 23 * n + 29) * a308815 (n - 2) +
    65536 * (n - 2) * (2 * n - 5) * a308815 (n - 3) = 0


private theorem cat_ode :
    X*(1-4*X)*derivative (R := ℚ) (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)) +
      (1-2*X)*(PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)) = 1 := by
  have cat_quad : X*(PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))^2 -
      PowerSeries.catalanSeries.map (Nat.castRingHom ℚ) + 1 = 0 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simp only [map_add, map_pow, map_mul, map_X, map_one] at h
    linear_combination h
  have h := congrArg (derivative (R := ℚ)) cat_quad
  simp only [map_add, map_sub, Derivation.leibniz, derivative_pow, derivative_one,
    derivative_X, map_zero, smul_eq_mul] at h
  norm_num at h
  linear_combination X*(2*X*(PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))-1)*h -
    (2*(PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))*X +
      4*derivative (R := ℚ) (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))*X^2 + 1)*cat_quad

private theorem p_coeff (n k : ℕ) : coeff k ((1 - 2 * X)^n) = (-2 : ℚ)^k * (n.choose k : ℚ) := by
  have h : (1 - 2 * X)^n =
      rescale (-2) (((1+Polynomial.X)^n : Polynomial ℚ) : (PowerSeries ℚ)) := by
    simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_X, map_pow, map_add, map_one, rescale_X, map_neg,
      map_ofNat C 2]
    congr 1
    ring
  rw [h, coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private noncomputable def b (n : ℕ) : ℚ :=
  coeff (2*n) ((1 - 2 * X)^n*(PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)))

private theorem b_sum (n : ℕ) : b n =
    ∑ i ∈ range (n+1), (-2 : ℚ)^i * (n.choose i : ℚ) * (catalan (2*n-i) : ℚ) := by
  rw [b, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [p_coeff]
  simp only [coeff_map, PowerSeries.catalanSeries_coeff, Nat.castRingHom]
  symm
  apply sum_subset (by intro i hi; simp only [mem_range] at hi ⊢; omega)
  intro i hi hni
  rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hi hni; omega)]
  simp

private theorem a_eq (n : ℕ) : (a308815 n : ℚ) = 16^n*b n := by
  rw [b_sum]
  simp [a308815]

private noncomputable def r (n : ℚ) : (PowerSeries ℚ) :=
  C (-n) + C (n+1)*X + C (6*n-6)*X^2 + C (-2*n-6)*X^3 + C (8-4*n)*X^4
private noncomputable def H (n : ℚ) : (PowerSeries ℚ) :=
  C (n*(2*n+1))*(1 - 2 * X)^3 - C (2*(9*n-4)*(n-1))*X^2*(1 - 2 * X)^2 +
    C (4*(3*n^2-23*n+29))*X^4*(1 - 2 * X) + C (16*(n-2)*(2*n-5))*X^6
private noncomputable def U (m : ℕ) : PowerSeries ℚ :=
  (1 - 2 * X)^(m+1)*(1-4*X)*r (m+3)*
    (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))

private theorem r_deriv (n : ℚ) : derivative (R := ℚ) (r n) =
  C (n+1) + C (2*(6*n-6))*X + C (3*(-2*n-6))*X^2 + C (4*(8-4*n))*X^3 := by
  simp [r, Derivation.leibniz, smul_eq_mul]
  simp only [map_ofNat C 2, map_ofNat C 3, map_ofNat C 4, map_ofNat C 6, map_ofNat C 8]
  ring

private theorem certificate (m : ℕ) :
    X*derivative (R := ℚ) (U m) - C (2*((m : ℚ)+3))*U m =
      H ((m : ℚ)+3)*(1 - 2 * X)^m*
        (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)) +
      (1 - 2 * X)^(m+1)*r ((m : ℚ)+3) := by
  dsimp [U]
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz,
    derivative_pow, r_deriv]
  simp only [map_sub, map_mul, derivative_one, Derivation.leibniz, ← map_ofNat C 2, ← map_ofNat C 4,
    derivative_C, derivative_X,
    smul_eq_mul, mul_zero, mul_one, zero_sub]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  dsimp [H, r]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    map_one C, map_ofNat C 2, map_ofNat C 3, map_ofNat C 4,
    map_ofNat C 5, map_ofNat C 6, map_ofNat C 8, map_ofNat C 9,
    map_ofNat C 16, map_ofNat C 23, map_ofNat C 29, map_natCast C]
  linear_combination ((1-2*X)^m * ((-(m:(PowerSeries ℚ))-3) +
    ((m:(PowerSeries ℚ))+4)*X + (6*(m:(PowerSeries ℚ))+12)*X^2 +
    (-2*(m:(PowerSeries ℚ))-12)*X^3 + (-4*(m:(PowerSeries ℚ))-4)*X^4) * (1-2*X)) * cat_ode


private theorem high_p (m j : ℕ) (hj : j ≤ 4) :
    coeff (2*(m+3)) (X^j*(1 - 2 * X : PowerSeries ℚ)^(m+1)) = 0 := by
  rw [coeff_X_pow_mul', if_pos (by omega), p_coeff,
    Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem forcing_zero (m : ℕ) :
    coeff (2*(m+3)) ((1 - 2 * X)^(m+1)*r ((m : ℚ)+3)) = 0 := by
  have hr : (1 - 2 * X)^(m+1)*r ((m : ℚ)+3) =
      C (-((m : ℚ)+3))*(X^0*(1 - 2 * X)^(m+1)) +
      C ((m : ℚ)+3+1)*(X^1*(1 - 2 * X)^(m+1)) +
      C (6*((m : ℚ)+3)-6)*(X^2*(1 - 2 * X)^(m+1)) +
      C (-2*((m : ℚ)+3)-6)*(X^3*(1 - 2 * X)^(m+1)) +
      C (8-4*((m : ℚ)+3))*(X^4*(1 - 2 * X)^(m+1)) := by dsimp [r]; ring
  rw [hr]
  simp only [map_add (coeff (2*(m+3))), coeff_C_mul, high_p m 0 (by omega), high_p m 1 (by omega),
    high_p m 2 (by omega), high_p m 3 (by omega), high_p m 4 (by omega),
    mul_zero, add_zero]

private theorem euler_coeff (f : (PowerSeries ℚ)) (d : ℕ) :
    coeff d (X*derivative (R := ℚ) f) = (d : ℚ)*coeff d f := by
  cases d with
  | zero => simp
  | succ d => simp [coeff_succ_X_mul, coeff_derivative, mul_comm]

private theorem annihilation (m : ℕ) :
    coeff (2*(m+3)) (H ((m : ℚ)+3)*(1 - 2 * X)^m*
      (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))) = 0 := by
  have h := congrArg (coeff (2*(m+3))) (certificate m)
  simp only [map_add, map_sub, coeff_C_mul, euler_coeff, forcing_zero,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h
  linear_combination -h

private theorem b_recurrence (m : ℕ) :
    ((m : ℚ)+3)*(2*((m : ℚ)+3)+1)*b (m+3) -
      2*(9*((m : ℚ)+3)-4)*((m : ℚ)+2)*b (m+2) +
      4*(3*((m : ℚ)+3)^2-23*((m : ℚ)+3)+29)*b (m+1) +
      16*((m : ℚ)+1)*(2*((m : ℚ)+3)-5)*b m = 0 := by
  have hex : H ((m : ℚ)+3)*(1 - 2 * X)^m*
      (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)) =
      C (((m : ℚ)+3)*(2*((m : ℚ)+3)+1))*((1 - 2 * X)^(m+3)*
        (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ))) -
      C (2*(9*((m : ℚ)+3)-4)*((m : ℚ)+2))*(X^2*((1 - 2 * X)^(m+2)*
        (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)))) +
      C (4*(3*((m : ℚ)+3)^2-23*((m : ℚ)+3)+29))*(X^4*((1 - 2 * X)^(m+1)*
        (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)))) +
      C (16*((m : ℚ)+1)*(2*((m : ℚ)+3)-5))*(X^6*((1 - 2 * X)^m*
        (PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)))) := by
    dsimp [H]
    simp only [pow_add, map_add, map_sub, map_mul, map_pow, map_one C,
      map_ofNat C 2, map_ofNat C 3, map_ofNat C 4, map_ofNat C 5,
      map_ofNat C 9, map_ofNat C 16, map_ofNat C 23, map_ofNat C 29, map_natCast C]
    ring
  have h := annihilation m
  rw [hex] at h
  simp only [map_add, map_sub, coeff_C_mul] at h
  rw [coeff_X_pow_mul', if_pos (by omega), coeff_X_pow_mul', if_pos (by omega),
    coeff_X_pow_mul', if_pos (by omega)] at h
  rw [show 2*(m+3)-2=2*(m+2) by omega,
    show 2*(m+3)-4=2*(m+1) by omega, show 2*(m+3)-6=2*m by omega] at h
  exact h

theorem result : claim := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m+3 := ⟨n-3, by omega⟩
  rw [show m+3-1=m+2 by omega, show m+3-2=m+1 by omega, show m+3-3=m by omega]
  have h := b_recurrence m
  have ha :
      (((m+3 : ℕ) : ℚ))*(2*(m+3)+1)*(a308815 (m+3) : ℚ) -
      32*(9*(m+3)-4)*(m+3-1)*(a308815 (m+2) : ℚ) +
      1024*(3*(m+3)^2-23*(m+3)+29)*(a308815 (m+1) : ℚ) +
      65536*(m+3-2)*(2*(m+3)-5)*(a308815 m : ℚ) = 0 := by
    simp only [a_eq, Nat.cast_add, Nat.cast_ofNat, pow_add]
    norm_num
    linear_combination 4096*(16:ℚ)^m*h
  exact_mod_cast ha

end D5.S1.Recurrence.A308815DFiniteRecurrence
