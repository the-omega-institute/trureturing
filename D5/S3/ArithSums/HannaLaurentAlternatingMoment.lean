/- GID: D5/S3/ArithSums/HannaLaurentAlternatingMoment
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaLaurentAlternatingMoment
   mirror-E: none(waiver:symbolic-laurent-coefficient-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: none
   digest: The alternating first moments of A391810 have generating function z(1-z+8z^2)/((1+z)^2(1-2z)^2). -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#228)
escape_witness: deriv_closed (27 P_n'(-1) = (15n - 11) 2^n + (11 - 30n)(-1)^n), obtained from
  the per-summand values d_odd / d_even, the splitting deriv_split, and the two-step
  recursions O_step, Q_step, Ev_step with their parity closed forms in `closed`.
proof_shape:
  d, O, Q, Ev: private definitions; consumers: the lemmas below.
  A, claim: source definitions; consumer: result.
  d_eq: bind-only helper (derivative rules); consumers: d_odd, d_even.
  d_odd, d_even: content (values at -1); consumer: deriv_split.
  Q_step, O_step, Ev_step: content (two-step recursions); consumer: closed.
  closed: content; consumer: deriv_closed.
  deriv_split: content; consumer: deriv_closed.
  deriv_closed: content; consumer: A_closed.
  A_eq: bind-only helper (derivative_eval over the row bound); consumers: A_closed, result.
  A_closed: bind-only helper; consumer: gf.
  gf: content (the order-four recurrence and initial values); consumer: result.
  result: content via gf and A_eq.
Direct frozen dependencies: D5/S3/ArithSums/HannaLaurentRowSums (series, rowPolynomial,
  rowBound, rowEntry, series_coefficient, row_degree; statement_id
  sha256:89abf5019c65efcb770839f6bd1a4c6fe94a2cdd7a25c6d4fa3d1022edf70f88).
Search record (§3.1): HannaLaurentFirstMoment proves the ordinary first moment (P_n'(1) = 1)
  and HannaLaurentSecondMoment the second; HannaLaurentAlternatingJacobsthal evaluates
  P_n(-1). No D5 declaration evaluates P_n'(-1) or its generating function.
-/

import D5.S3.ArithSums.HannaLaurentRowSums
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerSeries.Basic

/-! # A391810: the alternating first moment

For `n ≥ 1` let `T(n,k)` be the coefficient of `x^(-k)` in the Laurent expansion of
`∑_j x^j (1 - x^j)^(n + j)` and `P_n(y) = -1 + ∑_{h=1}^n y^h (1 - y^h)^(n - h)`. At `y = -1` the
summand with odd `h` has derivative `h (n - h + 2) 2^(n - h - 1)`, and with even `h` only
`h = n` and `h = n - 1` contribute `-n` and `n - 1`. Summing by two-step recursions gives
`27 A_n = (15 n - 11) 2^n + (11 - 30 n)(-1)^n` for `A_n = P_n'(-1)`, and hence
`∑_{n ≥ 1} A_n z^n = z (1 - z + 8 z^2) / ((1 + z)^2 (1 - 2 z)^2)`.
-/

set_option autoImplicit false

namespace D5.S3.ArithSums.HannaLaurentAlternatingMoment

open Polynomial
open D5.S3.ArithSums.HannaLaurentRowSums

noncomputable section

/-- The derivative at `-1` of the summand `X^h (1 - X^h)^m`. -/
private noncomputable def d (h m : ℕ) : ℤ := ((X ^ h * (1 - X ^ h) ^ m : ℤ[X]).derivative).eval (-1)

private theorem d_eq (h m : ℕ) : d h m =
    h * (-1) ^ (h - 1) * (1 - (-1) ^ h) ^ m
      - (-1) ^ h * (m * (1 - (-1) ^ h) ^ (m - 1) * (h * (-1) ^ (h - 1))) := by
  simp [d, derivative_mul, derivative_pow, derivative_sub]
  ring

private theorem d_odd (h m : ℕ) (hh : h % 2 = 1) : 2 * d h m = h * (m + 2) * 2 ^ m := by
  rw [d_eq]
  have h1 : ((-1 : ℤ)) ^ h = -1 := by
    rw [← Nat.mod_add_div h 2, hh, pow_add, pow_mul]; norm_num
  have h2 : ((-1 : ℤ)) ^ (h - 1) = 1 := by
    have : h - 1 = 2 * (h / 2) := by omega
    rw [this, pow_mul]; norm_num
  rw [h1, h2]
  rcases m with _ | m
  · simp; ring
  · simp only [Nat.add_sub_cancel]
    norm_num
    ring

private theorem d_even (h m : ℕ) (hh : h % 2 = 0) (hpos : 1 ≤ h) :
    d h m = if m = 0 then -(h : ℤ) else if m = 1 then (h : ℤ) else 0 := by
  rw [d_eq]
  have h1 : ((-1 : ℤ)) ^ h = 1 := by
    rw [← Nat.mod_add_div h 2, hh, pow_add, pow_mul]; norm_num
  have h2 : ((-1 : ℤ)) ^ (h - 1) = -1 := by
    have : h - 1 = 2 * ((h - 2) / 2) + 1 := by omega
    rw [this, pow_add, pow_mul]; norm_num
  rw [h1, h2]
  rcases m with _ | _ | m
  · simp
  · simp
  · simp

/-- Odd-index weights `h (m + 2) 2^m` at `h = j + 1`, `m = n - h`. -/
private def O (n : ℕ) : ℤ := ∑ j ∈ Finset.range n,
  if (j + 1) % 2 = 1 then ((j + 1 : ℕ) : ℤ) * (((n - (j + 1) : ℕ) : ℤ) + 2) * 2 ^ (n - (j + 1))
  else 0

/-- Odd-index weights `h 2^m`. -/
private def Q (n : ℕ) : ℤ := ∑ j ∈ Finset.range n,
  if (j + 1) % 2 = 1 then ((j + 1 : ℕ) : ℤ) * 2 ^ (n - (j + 1)) else 0

/-- Even-index boundary contributions, doubled. -/
private def Ev (n : ℕ) : ℤ := ∑ j ∈ Finset.range n,
  if (j + 1) % 2 = 0 then 2 * (if n - (j + 1) = 0 then -((j + 1 : ℕ) : ℤ)
    else if n - (j + 1) = 1 then ((j + 1 : ℕ) : ℤ) else 0) else 0

private theorem Q_step (n : ℕ) : Q (n + 2) = 4 * Q n +
    (if (n + 1) % 2 = 1 then 2 * ((n + 1 : ℕ) : ℤ) else 0) +
    (if (n + 2) % 2 = 1 then ((n + 2 : ℕ) : ℤ) else 0) := by
  unfold Q
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.mul_sum]
  congr 2
  · apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [show n + 2 - (j + 1) = (n - (j + 1)) + 2 by omega, pow_add]
    split_ifs <;> ring
  · rw [show n + 2 - (n + 1) = 1 by omega]; split_ifs <;> ring
  · rw [show n + 2 - (n + 1 + 1) = 0 by omega]; push_cast; ring

private theorem O_step (n : ℕ) : O (n + 2) = 4 * O n + 8 * Q n +
    (if (n + 1) % 2 = 1 then 6 * ((n + 1 : ℕ) : ℤ) else 0) +
    (if (n + 2) % 2 = 1 then 2 * ((n + 2 : ℕ) : ℤ) else 0) := by
  unfold O Q
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 2
  · apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [show n + 2 - (j + 1) = (n - (j + 1)) + 2 by omega, pow_add]
    split_ifs
    · push_cast; ring
    · ring
  · rw [show n + 2 - (n + 1) = 1 by omega]; split_ifs <;> ring
  · rw [show n + 2 - (n + 1 + 1) = 0 by omega]; push_cast; ring

private theorem Ev_step (n : ℕ) : Ev (n + 2) =
    (if (n + 1) % 2 = 0 then 2 * ((n + 1 : ℕ) : ℤ) else 0) +
    (if (n + 2) % 2 = 0 then -2 * ((n + 2 : ℕ) : ℤ) else 0) := by
  unfold Ev
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [Finset.sum_eq_zero (fun j hj => by
    have hj := Finset.mem_range.mp hj
    have h3 : n + 1 - j ≠ 0 := by omega
    have h4 : n + 1 - j ≠ 1 := by omega
    simp [h3, h4])]
  rw [show n + 2 - (n + 1) = 1 by omega, show n + 2 - (n + 1 + 1) = 0 by omega]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have a1 : (n + 1) % 2 = 1 := by omega
    have a2 : (n + 1 + 1) % 2 = 0 := by omega
    have a3 : (n + 2) % 2 = 0 := by omega
    simp [a1, a2]
    ring
  · have a1 : (n + 1) % 2 = 0 := by omega
    have a2 : (n + 1 + 1) % 2 = 1 := by omega
    have a3 : (n + 2) % 2 = 1 := by omega
    simp [a1, a2]

private theorem closed (t : ℕ) :
    (27 * O (2 * t) = (60 * t - 22) * 4 ^ t - 12 * t + 22 ∧
      27 * O (2 * t + 1) = (120 * t + 16) * 4 ^ t + 12 * t + 38) ∧
    (18 * Q (2 * t) = 20 * 4 ^ t - 24 * t - 20 ∧
      18 * Q (2 * t + 1) = 40 * 4 ^ t - 12 * t - 22) ∧
    (Ev (2 * t) = -4 * t ∧ Ev (2 * t + 1) = 4 * t) := by
  induction t with
  | zero => simp [O, Q, Ev]
  | succ t ih =>
    obtain ⟨⟨o0, o1⟩, ⟨q0, q1⟩, -⟩ := ih
    have e0 : 2 * (t + 1) = 2 * t + 2 := by ring
    have e1 : 2 * t + 2 + 1 = 2 * t + 1 + 2 := by ring
    rw [e0, e1, O_step, O_step, Q_step, Q_step, Ev_step, Ev_step]
    have p1 : (2 * t + 1) % 2 = 1 := by omega
    have p2 : (2 * t + 2) % 2 = 0 := by omega
    have p3 : (2 * t + 1 + 1) % 2 = 0 := by omega
    have p4 : (2 * t + 1 + 2) % 2 = 1 := by omega
    simp only [p1, p2, p4, ite_true, ite_false, one_ne_zero, zero_ne_one]
    push_cast
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [pow_succ]; linear_combination 4 * o0 + 12 * q0
    · rw [pow_succ]; linear_combination 4 * o1 + 12 * q1
    · rw [pow_succ]; linear_combination 4 * q0
    · rw [pow_succ]; linear_combination 4 * q1
    · ring
    · ring


private theorem deriv_split (n : ℕ) :
    2 * ((rowPolynomial n).derivative).eval (-1) = O n + Ev n := by
  have hd : ((rowPolynomial n).derivative).eval (-1) =
      ∑ j ∈ Finset.range n, d (j + 1) (n - (j + 1)) := by
    simp only [rowPolynomial, derivative_add, derivative_neg, derivative_one, neg_zero,
      zero_add, derivative_sum, eval_finsetSum, d]
  rw [hd, Finset.mul_sum, O, Ev, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases Nat.mod_two_eq_zero_or_one (j + 1) with h | h
  · rw [d_even _ _ h (by omega)]
    simp only [h, zero_ne_one, ite_false, ite_true]
    ring
  · rw [d_odd _ _ h]
    simp only [h, one_ne_zero, ite_false, ite_true]
    push_cast
    ring

private theorem deriv_closed (n : ℕ) :
    27 * ((rowPolynomial n).derivative).eval (-1) =
      (15 * n - 11) * 2 ^ n + (11 - 30 * n) * (-1) ^ n := by
  have h2 := deriv_split n
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2 * t ∨ n = 2 * t + 1 := ⟨n / 2, by omega⟩
  · obtain ⟨⟨o0, -⟩, -, e0, -⟩ := closed t
    have hp : (2 : ℤ) ^ (2 * t) = 4 ^ t := by rw [pow_mul]; norm_num
    have hm : (-1 : ℤ) ^ (2 * t) = 1 := by rw [pow_mul]; norm_num
    rw [hp, hm]
    push_cast
    linear_combination 27 * h2 + o0 + 27 * e0
  · obtain ⟨⟨-, o1⟩, -, -, e1⟩ := closed t
    have hp : (2 : ℤ) ^ (2 * t + 1) = 2 * 4 ^ t := by rw [pow_succ, pow_mul]; norm_num; ring
    have hm : (-1 : ℤ) ^ (2 * t + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hp, hm]
    push_cast
    linear_combination 27 * h2 + o1 + 27 * e1

/-- The alternating first moment `A_n = -∑ (-1)^k k T(n,k)` of row `n`. -/
noncomputable def A (n : ℕ) : ℤ :=
  -∑ k ∈ Finset.range (rowBound n + 1), (-1) ^ k * (k : ℤ) * rowEntry n k

private theorem A_eq (n : ℕ) : A n = ((rowPolynomial n).derivative).eval (-1) := by
  have h := Polynomial.derivative_eval (rowPolynomial n) (-1 : ℤ)
  rw [Polynomial.sum_over_range' _ (by simp) (rowBound n + 1)
    (Nat.lt_succ_of_le (row_degree n))] at h
  rw [h, A, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rcases k with _ | k
  · simp
  · simp only [rowEntry, Nat.add_sub_cancel, pow_succ]
    push_cast
    ring

private theorem A_closed (n : ℕ) : 27 * A n = (15 * n - 11) * 2 ^ n + (11 - 30 * n) * (-1) ^ n := by
  rw [A_eq]; exact deriv_closed n

private theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else A n) *
        ((1 + PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2) =
      PowerSeries.X * (1 - PowerSeries.X + 8 * PowerSeries.X ^ 2) := by
  have hA := A_closed
  have hval : ∀ n, (if n = 0 then (0 : ℤ) else A n) = A n := by
    intro n; split_ifs with h
    · subst h; have := hA 0; norm_num at this; omega
    · rfl
  simp_rw [hval]
  set f := PowerSeries.mk A with hf
  have hl : f * ((1 + PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2) =
      f - 2 * (f * PowerSeries.X ^ 1) - 3 * (f * PowerSeries.X ^ 2) +
        4 * (f * PowerSeries.X ^ 3) + 4 * (f * PowerSeries.X ^ 4) := by ring
  have hr : (PowerSeries.X : PowerSeries ℤ) * (1 - PowerSeries.X + 8 * PowerSeries.X ^ 2) =
      PowerSeries.X - PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3 := by ring
  rw [hl, hr]
  have v0 : A 0 = 0 := by have := hA 0; norm_num at this; omega
  have v1 : A 1 = 1 := by have := hA 1; norm_num at this; omega
  have v2 : A 2 = 1 := by have := hA 2; norm_num at this; omega
  have v3 : A 3 = 13 := by have := hA 3; norm_num at this; omega
  ext k
  rcases k with _ | _ | _ | _ | t
  · simp [hf, v0]
  · simp [hf, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_X, v0, v1]
  · simp [hf, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_X, v0, v1, v2]
  · simp [hf, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_X, v0, v1, v2, v3]
  · simp [hf, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
    apply mul_left_cancel₀ (show (27 : ℤ) ≠ 0 by norm_num)
    have a0 := hA t
    have a1 := hA (t + 1)
    have a2 := hA (t + 2)
    have a3 := hA (t + 3)
    have a4 := hA (t + 1 + 1 + 1 + 1)
    push_cast at a1 a2 a3 a4
    linear_combination a4 - 2 * a3 - 3 * a2 + 4 * a1 + 4 * a0


/-- Formula (6) of A391810: `A_n = -∑ (-1)^k k T(n,k) = P_n'(-1)` for `n ≥ 1`, with the
literal Laurent coefficients, and the ordinary generating function of `A_n` over `n ≥ 1`. -/
def claim : Prop :=
  (∀ (n : ℕ) (hn : 0 < n), (A n : ℚ) =
      -∑ k ∈ Finset.range (rowBound n + 1), (-1) ^ k * (k : ℚ) * (series n hn).coeff (-(k : ℤ))) ∧
    (∀ n : ℕ, 0 < n → A n = ((rowPolynomial n).derivative).eval (-1)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else A n) *
        ((1 + PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2) =
      PowerSeries.X * (1 - PowerSeries.X + 8 * PowerSeries.X ^ 2)

theorem result : claim := by
  refine ⟨fun n hn => ?_, fun n _ => A_eq n, gf⟩
  simp_rw [series_coefficient]
  rw [A]
  push_cast
  rfl

end

end D5.S3.ArithSums.HannaLaurentAlternatingMoment
