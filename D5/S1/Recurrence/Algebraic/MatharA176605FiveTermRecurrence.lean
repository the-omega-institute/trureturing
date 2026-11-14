/- GID: D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: []
   utility: none
   digest: The original nonlinear convolution A176605 satisfies Mathar's complete five-term identity. -/

/-
admission_basis: open-problem-resolution (#30568).
proof_shape: bind-only; escape_witness: none.
The result uses source conditions only at m ≥ 1. All signed arithmetic is
performed after casting the index and sequence values into the integers.
The source omits the linear onset; n ≥ 4 is the nonnegative-backshift
interpretation and is independent of the entry's OFFSET.
The private helpers are consumed as follows:
  coeff_sq → source_equation; source_equation → result;
  derivative_equation → result; certificate → result.
The definitions sourceSeries, F, P, Q, R, K and L occur on those proof paths.
The actual natural sequence source is consumed by the Reg source_conditions
and changed_law proofs, establishing nonvacuity of the original conditions.
The direct frozen supplier is A308815DFiniteRecurrence.euler_coeff.
The source attribution and literature boundary are in
Library/RecurrenceAlgebraic/mathar2016a176605.md.
All declarations concern unbounded formal identities or the actual recursive
source; none is bounded enumeration, a numerical reduction or an isolated
certified finite instance. Thus utility is none.
-/

import D5.S1.Recurrence.A308815DFiniteRecurrence
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-! The original nonlinear convolution implies the complete Mathar five-term identity. -/

set_option autoImplicit false
set_option maxRecDepth 4096
open scoped BigOperators
open Finset PowerSeries
namespace D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence

/-- The actual natural-valued convolution sequence, with its exceptional first step. -/
def source : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | m + 2 => (∑ p : Fin (m + 2), source p * source (m + 1-p)) + 1
termination_by n => n
decreasing_by
  all_goals have hp := p.isLt; omega


private noncomputable def sourceSeries (a : ℕ → ℕ) : PowerSeries ℚ :=
  mk (fun n => (a n : ℚ))

private noncomputable def F (A : PowerSeries ℚ) : PowerSeries ℚ :=
  X * (1 - X) * A ^ 2 - (1 - X) * A + 1 - X + X ^ 2

private noncomputable def P : PowerSeries ℚ := 1 - 6 * X + 9 * X ^ 2 - 8 * X ^ 3 + 4 * X ^ 4
private noncomputable def Q : PowerSeries ℚ := 1 - 4 * X + 5 * X ^ 2
private noncomputable def R : PowerSeries ℚ := 1 - 2 * X + 4 * X ^ 2 - 2 * X ^ 3
private noncomputable def K : PowerSeries ℚ := 1 - 4 * X ^ 2 + 8 * X ^ 3
private noncomputable def L : PowerSeries ℚ := 1 - 5 * X + 4 * X ^ 2 - 4 * X ^ 3

def claim : Prop := ∀ (a : ℕ → ℕ),
  a 0 = 1 → a 1 = 1 →
  (∀ m : ℕ, 1 ≤ m → a (m + 1) = ∑ p ∈ range (m + 1), a p * a (m-p) + 1) →
  ∀ n : ℕ, 4 ≤ n →
    (((n:ℤ) + 1) * (a n : ℤ) + 2 * (-3 * (n:ℤ) + 1) * (a (n-1) : ℤ) +
      (9 * (n:ℤ)-13) * (a (n-2) : ℤ) + 8 * (-(n:ℤ) + 3) * (a (n-3) : ℤ) +
      4 * ((n:ℤ)-4) * (a (n-4) : ℤ) = 0)

private theorem coeff_sq (a : ℕ → ℕ) (n : ℕ) :
    coeff n ((sourceSeries a) ^ 2) =
      ∑ p ∈ range (n + 1), ((a p : ℚ) * (a (n-p) : ℚ)) := by
  rw [pow_two, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [sourceSeries, coeff_mk]

set_option maxHeartbeats 800000 in
-- Coefficient expansion and the elimination certificate contain several polynomial products.
private theorem source_equation (a : ℕ → ℕ)
    (ha0 : a 0 = 1) (ha1 : a 1 = 1)
    (hr : ∀ m : ℕ, 1 ≤ m → a (m + 1) = ∑ p ∈ range (m + 1), a p * a (m-p) + 1) :
    F (sourceSeries a) = 0 := by
  ext n
  rw [show F (sourceSeries a) =
      X ^ 1 * (sourceSeries a) ^ 2 - X ^ 2 * (sourceSeries a) ^ 2 - sourceSeries a +
        X ^ 1 * sourceSeries a + 1 - X + X ^ 2 by
        dsimp [F]; ring]
  simp only [map_add, map_sub, map_zero, coeff_X_pow_mul', coeff_one, coeff_X, coeff_X_pow,
    coeff_sq]
  simp only [sourceSeries, coeff_mk]
  cases n with
  | zero => simp [ha0]
  | succ n =>
    cases n with
    | zero => simp [ha0, ha1]
    | succ m =>
      have hm := hr (m + 1) (by omega)
      rw [show m + 1 + 1 = m + 2 by omega] at hm
      push_cast
      have hmq : (a (m + 2) : ℚ) =
          ∑ p ∈ range (m + 2), (a p : ℚ) * (a (m + 1-p) : ℚ) + 1 := by
        exact_mod_cast hm
      change (∑ p ∈ range (m + 2), (a p : ℚ) * (a (m + 1-p) : ℚ)) -
        (∑ p ∈ range (m + 1), (a p : ℚ) * (a (m-p) : ℚ)) -
        (a (m + 2) : ℚ) + (a (m + 1) : ℚ) + 0 - 0 +
        (if m = 0 then (1:ℚ) else 0) = 0
      rw [hmq]
      cases m with
      | zero => simp [ha0, ha1] <;> ring
      | succ m =>
        have hprev : (a (m + 2) : ℚ) =
            (∑ p ∈ range (m + 2), (a p : ℚ) * (a (m + 1-p) : ℚ)) + 1 := by
          exact_mod_cast hr (m + 1) (by omega)
        rw [hprev]
        simp <;> ring

private theorem derivative_equation (A : PowerSeries ℚ) (hF : F A = 0) :
    2 * X * (1 - X) * A * (X * derivative A) - (1 - X) * (X * derivative A) +
      X * (1 - 2 * X) * A ^ 2 + X * A + X * (-1 + 2 * X) = 0 := by
  have hd := congrArg (derivative (R := ℚ)) hF
  dsimp [F] at hd
  simp only [map_sub, map_add, derivative_X, derivative_one,
    derivative_pow, Derivation.leibniz, smul_eq_mul, add_zero, map_zero] at hd
  linear_combination X * hd

set_option maxHeartbeats 800000 in
-- Coefficient expansion and the elimination certificate contain several polynomial products.
private theorem certificate (A : PowerSeries ℚ) (hF : F A = 0)
    (hD : 2 * X * (1 - X) * A * (X * derivative A) - (1 - X) * (X * derivative A) +
      X * (1 - 2 * X) * A ^ 2 + X * A + X * (-1 + 2 * X) = 0) :
    P * (X * derivative A) + Q * A = R := by
  have hc : (2 * X * A-1) * (P * (X * derivative A) + Q * A - R) =
      K * F A + L * (2 * X * (1 - X) * A * (X * derivative A) - (1 - X) * (X * derivative A) +
      X * (1 - 2 * X) * A ^ 2 + X * A + X * (-1 + 2 * X)) := by
    dsimp [P,Q,R,K,L,F]
    ring
  have hz : (2 * X * A-1) ≠ 0 := by
    intro hz
    have hc0 := congrArg constantCoeff hz
    norm_num at hc0
  have hzero : (2 * X * A-1) * (P * (X * derivative A) + Q * A - R) = 0 := by
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
  have hex : P * (X * derivative A) + Q * A =
      (X * derivative A) - 6 * (X ^ 1 * (X * derivative A)) +
      9 * (X ^ 2 * (X * derivative A)) - 8 * (X ^ 3 * (X * derivative A)) +
      4 * (X ^ 4 * (X * derivative A)) + A - 4 * (X ^ 1 * A) + 5 * (X ^ 2 * A) := by
    dsimp [P,Q]; ring
  rw [hex] at hO
  have hh := congrArg (coeff n) hO
  have hR : coeff n R = 0 := by
    simp only [R, map_add, map_sub, coeff_one, coeff_ofNat_mul, coeff_X, coeff_X_pow]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega]
  rw [hR] at hh
  simp only [map_add, map_sub, coeff_ofNat_mul] at hh
  simp only [coeff_X_pow_mul', ite_eq_left (by omega : 1 ≤ n), ite_eq_left (by omega : 2 ≤ n),
    ite_eq_left (by omega : 3 ≤ n), ite_eq_left hn,
    D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff] at hh
  simp only [A, sourceSeries, coeff_mk] at hh
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub hn] at hh
  have hq : ((n:ℚ) + 1) * (a n : ℚ) + 2 * (-3 * (n:ℚ) + 1) * (a (n-1) : ℚ) +
      (9 * (n:ℚ)-13) * (a (n-2) : ℚ) + 8 * (-(n:ℚ) + 3) * (a (n-3) : ℚ) +
      4 * ((n:ℚ)-4) * (a (n-4) : ℚ) = 0 := by linear_combination hh
  exact_mod_cast hq

end D5.S1.Recurrence.Algebraic.MatharA176605FiveTermRecurrence
