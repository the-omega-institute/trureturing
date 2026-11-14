import D5.S1.Recurrence.A308815DFiniteRecurrence
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open scoped BigOperators
open Finset PowerSeries
namespace D5.S1.Recurrence.Algebraic.A176605Probe

noncomputable def sourceSeries (a : ℕ → ℕ) : PowerSeries ℚ :=
  mk (fun n => (a n : ℚ))

noncomputable def F (A : PowerSeries ℚ) : PowerSeries ℚ :=
  X * (1 - X) * A ^ 2 - (1 - X) * A + 1 - X + X ^ 2

noncomputable def P : PowerSeries ℚ := 1 - 6*X + 9*X^2 - 8*X^3 + 4*X^4
noncomputable def Q : PowerSeries ℚ := 1 - 4*X + 5*X^2
noncomputable def R : PowerSeries ℚ := 1 - 2*X + 4*X^2 - 2*X^3
noncomputable def K : PowerSeries ℚ := 1 - 4*X^2 + 8*X^3
noncomputable def L : PowerSeries ℚ := 1 - 5*X + 4*X^2 - 4*X^3

def claim : Prop := ∀ (a : ℕ → ℕ),
  a 0 = 1 → a 1 = 1 →
  (∀ m : ℕ, 1 ≤ m → a (m+1) = ∑ p ∈ range (m+1), a p * a (m-p) + 1) →
  ∀ n : ℕ, 4 ≤ n →
    ((n+1 : ℤ) * (a n : ℤ) + 2 * (-3*(n:ℤ)+1) * (a (n-1) : ℤ) +
      (9*(n:ℤ)-13) * (a (n-2) : ℤ) + 8 * (-(n:ℤ)+3) * (a (n-3) : ℤ) +
      4 * ((n:ℤ)-4) * (a (n-4) : ℤ) = 0)

private theorem coeff_sq (a : ℕ → ℕ) (n : ℕ) :
    coeff n ((sourceSeries a)^2) =
      ∑ p ∈ range (n+1), ((a p : ℚ) * (a (n-p) : ℚ)) := by
  rw [pow_two, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [sourceSeries, coeff_mk]

private theorem source_equation (a : ℕ → ℕ)
    (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (hr : ∀ m : ℕ, 1 ≤ m → a (m+1) = ∑ p ∈ range (m+1), a p * a (m-p) + 1) :
    F (sourceSeries a) = 0 := by
  ext n
  have hs := coeff_sq a
  rw [show F (sourceSeries a) =
      X * (sourceSeries a)^2 - X^2 * (sourceSeries a)^2 - sourceSeries a +
        X * sourceSeries a + 1 - X + X^2 by
        dsimp [F]; ring]
  rw [map_sub, map_add, map_sub, map_add, map_sub]
  simp only [coeff_add, coeff_sub, coeff_X_pow_mul', coeff_one, coeff_X, coeff_mk,
    coeff_ofNat_mul, mul_zero, zero_mul, one_mul, coeff_sq]
  cases n with
  | zero => simp [ha0]
  | succ n =>
    cases n with
    | zero => simp [ha0, ha1]
    | succ m =>
      have hm := hr (m+1) (by omega)
      rw [show m + 1 + 1 = m + 2 by omega] at hm
      push_cast
      rw [show (m+2) - 1 = m+1 by omega, show (m+2)-2=m by omega]
      simp only [Nat.cast_add, Nat.cast_one]
      have hmq : (a (m+2) : ℚ) =
          ∑ p ∈ range (m+2), (a p : ℚ) * (a (m+1-p) : ℚ) + 1 := by
        exact_mod_cast hm
      rw [hmq]
      have hprev : (a (m+1) : ℚ) =
          (∑ p ∈ range (m+1), (a p : ℚ) * (a (m-p) : ℚ)) + 1 := by
        by_cases h : m = 0
        · subst m; simp [ha1, ha0]
        · have hh := hr m (by omega)
          exact_mod_cast hh
      rw [hprev]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [← Finset.sum_range_succ']
      simp only [Nat.add_sub_cancel, Nat.cast_one]
      ring

private theorem derivative_equation (A : PowerSeries ℚ) (hF : F A = 0) :
    2 * (1-X) * A * (X * derivative A) - (1-X) * (X * derivative A) +
      X * (1-2*X) * A^2 + X*A + X*(-1+2*X) = 0 := by
  have hd := congrArg (derivative (R := ℚ)) hF
  dsimp [F] at hd
  simp only [map_sub, map_add, map_mul, map_one, derivative_X, derivative_one,
    derivative_pow, Derivation.leibniz, smul_eq_mul, mul_zero, add_zero] at hd
  linear_combination X * hd

private theorem certificate (A : PowerSeries ℚ) (hF : F A = 0)
    (hD : 2 * (1-X) * A * (X * derivative A) - (1-X) * (X * derivative A) +
      X * (1-2*X) * A^2 + X*A + X*(-1+2*X) = 0) :
    P * (X * derivative A) + Q*A = R := by
  have hc : (2*X*A-1) * (P * (X*derivative A) + Q*A - R) =
      K * F A + L * (2 * (1-X) * A * (X * derivative A) - (1-X) * (X * derivative A) +
      X * (1-2*X) * A^2 + X*A + X*(-1+2*X)) := by
    dsimp [P,Q,R,K,L,F]
    ring
  have hz : (2*X*A-1) ≠ 0 := by
    intro hz
    have hc0 := congrArg constantCoeff hz
    simp only [map_sub, map_mul, map_one, constantCoeff_X_mul, zero_mul, sub_zero,
      map_ofNat] at hc0
    norm_num at hc0
  have hzero : (2*X*A-1) * (P * (X*derivative A) + Q*A - R) = 0 := by
    rw [hc, hF, hD]
    simp
  have := (mul_eq_zero.mp hzero).resolve_left hz
  exact sub_eq_zero.mp this

theorem result : claim := by
  intro a ha0 ha1 hr n hn
  let A := sourceSeries a
  have hF : F A = 0 := source_equation a ha0 ha1 hr
  have hD := derivative_equation A hF
  have hO := certificate A hF hD
  have hh := congrArg (coeff n) hO
  have hR : coeff n R = 0 := by
    simp [R]
    omega
  rw [hR] at hh
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul',
    D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff] at hh
  simp only [P,Q,A,sourceSeries] at hh
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n)] at hh
  exact_mod_cast hh

end D5.S1.Recurrence.Algebraic.A176605Probe
