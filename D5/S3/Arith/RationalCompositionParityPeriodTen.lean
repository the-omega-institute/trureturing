/- GID: D5/S3/Arith/RationalCompositionParityPeriodTen
   generality: I
   mirror-B: D5/B/S3/Arith/RationalCompositionParityPeriodTen
   mirror-E: none(waiver:symbolic-unbounded-parity-theorems)
   anchors: []
   utility: none
   digest: A396093 formula (2) has period ten modulo two, proving both parity conjectures. -/

import Mathlib.Data.Nat.Periodic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.RationalCompositionParityPeriodTen

noncomputable section

local notation "Xq" => (PowerSeries.X : PowerSeries ℚ)

/-- The factored numerator of formula (2), literally as a rational power series. -/
def N : PowerSeries ℚ :=
  Xq * (1 - Xq) ^ 2 * (1 - 3 * Xq + Xq ^ 2) ^ 2

/-- The squared denominator of formula (2), literally as a rational power series. -/
def D : PowerSeries ℚ :=
  (1 - 7 * Xq + 13 * Xq ^ 2 - 7 * Xq ^ 3 + Xq ^ 4) ^ 2

/-- The denominator coefficients expand the squared quartic in formula (2). -/
theorem denominator_expansion :
    D = 1 - 14 * Xq + 75 * Xq ^ 2 - 196 * Xq ^ 3 + 269 * Xq ^ 4 -
      196 * Xq ^ 5 + 75 * Xq ^ 6 - 14 * Xq ^ 7 + Xq ^ 8 := by
  simp only [D]
  ring

/-- The numerator coefficients expand the factored numerator in formula (2). -/
theorem numerator_expansion :
    N = Xq - 8 * Xq ^ 2 + 24 * Xq ^ 3 - 34 * Xq ^ 4 + 24 * Xq ^ 5 -
      8 * Xq ^ 6 + Xq ^ 7 := by
  simp only [N]
  ring

/-- OEIS A396093, defined by its first eight values and order-eight recurrence. -/
def a : Nat -> Int
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 33
  | 4 => 174
  | 5 => 892
  | 6 => 4480
  | 7 => 22149
  | n + 8 =>
      14 * a (n + 7) - 75 * a (n + 6) + 196 * a (n + 5) -
        269 * a (n + 4) + 196 * a (n + 3) - 75 * a (n + 2) +
          14 * a (n + 1) - a n

private theorem a_recurrence (n : Nat) :
    a (n + 8) =
      14 * a (n + 7) - 75 * a (n + 6) + 196 * a (n + 5) -
        269 * a (n + 4) + 196 * a (n + 3) - 75 * a (n + 2) +
          14 * a (n + 1) - a n := by
  simp [a]

/-- The homogeneous coefficient equations above degree seven in `A * D = N`. -/
theorem rational_tail_equation (n : Nat) :
    a (n + 8) - 14 * a (n + 7) + 75 * a (n + 6) - 196 * a (n + 5) +
        269 * a (n + 4) - 196 * a (n + 3) + 75 * a (n + 2) -
          14 * a (n + 1) + a n = 0 := by
  linear_combination a_recurrence n

private theorem a_zero : a 0 = 0 := by rfl
private theorem a_one : a 1 = 1 := by rfl
private theorem a_two : a 2 = 6 := by rfl
private theorem a_three : a 3 = 33 := by rfl
private theorem a_four : a 4 = 174 := by rfl
private theorem a_five : a 5 = 892 := by rfl
private theorem a_six : a 6 = 4480 := by rfl
private theorem a_seven : a 7 = 22149 := by rfl

private theorem a_eight : a 8 = 108144 := by
  have h := a_recurrence 0
  norm_num [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven] at h
  exact h

private theorem a_nine : a 9 = 522685 := by
  have h := a_recurrence 1
  norm_num [a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight] at h
  exact h

/-- The eight inhomogeneous coefficient equations in `A * D = N`. -/
theorem initial_coefficient_equations :
    a 0 = 0 ∧
    a 1 - 14 * a 0 = 1 ∧
    a 2 - 14 * a 1 + 75 * a 0 = -8 ∧
    a 3 - 14 * a 2 + 75 * a 1 - 196 * a 0 = 24 ∧
    a 4 - 14 * a 3 + 75 * a 2 - 196 * a 1 + 269 * a 0 = -34 ∧
    a 5 - 14 * a 4 + 75 * a 3 - 196 * a 2 + 269 * a 1 - 196 * a 0 = 24 ∧
    a 6 - 14 * a 5 + 75 * a 4 - 196 * a 3 + 269 * a 2 - 196 * a 1 +
      75 * a 0 = -8 ∧
    a 7 - 14 * a 6 + 75 * a 5 - 196 * a 4 + 269 * a 3 - 196 * a 2 +
      75 * a 1 - 14 * a 0 = 1 := by
  norm_num [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven]

private def lag (b : ℕ → ℚ) (n k : ℕ) : ℚ := if k ≤ n then b (n - k) else 0

private theorem coeff_mul_D (b : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk b * D) =
      b n - 14 * lag b n 1 + 75 * lag b n 2 - 196 * lag b n 3 +
        269 * lag b n 4 - 196 * lag b n 5 + 75 * lag b n 6 -
          14 * lag b n 7 + lag b n 8 := by
  let p := PowerSeries.mk b
  have h14 : (14 : PowerSeries ℚ) = PowerSeries.C (14 : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 14).symm
  have h75 : (75 : PowerSeries ℚ) = PowerSeries.C (75 : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 75).symm
  have h196 : (196 : PowerSeries ℚ) = PowerSeries.C (196 : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 196).symm
  have h269 : (269 : PowerSeries ℚ) = PowerSeries.C (269 : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 269).symm
  calc
    PowerSeries.coeff n (p * D) = PowerSeries.coeff n
        (p - PowerSeries.C 14 * (p * Xq) + PowerSeries.C 75 * (p * Xq ^ 2) -
          PowerSeries.C 196 * (p * Xq ^ 3) + PowerSeries.C 269 * (p * Xq ^ 4) -
          PowerSeries.C 196 * (p * Xq ^ 5) + PowerSeries.C 75 * (p * Xq ^ 6) -
          PowerSeries.C 14 * (p * Xq ^ 7) + p * Xq ^ 8) := by
      congr 1
      rw [denominator_expansion]
      simp only [h14, h75, h196, h269]
      ring
    _ = b n - 14 * lag b n 1 + 75 * lag b n 2 - 196 * lag b n 3 +
        269 * lag b n 4 - 196 * lag b n 5 + 75 * lag b n 6 -
          14 * lag b n 7 + lag b n 8 := by
      have hX : PowerSeries.coeff n (p * Xq) =
          if 1 ≤ n then b (n - 1) else 0 := by
        simpa only [pow_one, p, PowerSeries.coeff_mk] using
          PowerSeries.coeff_mul_X_pow' p 1 n
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, p]
      rw [hX]
      simp only [lag]

private theorem coeff_mul_D_tail (b : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 8) (PowerSeries.mk b * D) =
      b (n + 8) - 14 * b (n + 7) + 75 * b (n + 6) - 196 * b (n + 5) +
        269 * b (n + 4) - 196 * b (n + 3) + 75 * b (n + 2) -
          14 * b (n + 1) + b n := by
  rw [coeff_mul_D]
  simp [lag]

private theorem numerator_expansion_C :
    N = Xq - PowerSeries.C 8 * Xq ^ 2 + PowerSeries.C 24 * Xq ^ 3 -
      PowerSeries.C 34 * Xq ^ 4 + PowerSeries.C 24 * Xq ^ 5 -
        PowerSeries.C 8 * Xq ^ 6 + Xq ^ 7 := by
  have h8 : (8 : PowerSeries ℚ) = PowerSeries.C (8 : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8).symm
  have h24 : (24 : PowerSeries ℚ) = PowerSeries.C (24 : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 24).symm
  have h34 : (34 : PowerSeries ℚ) = PowerSeries.C (34 : ℚ) :=
    (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 34).symm
  simpa only [h8, h24, h34] using numerator_expansion

private theorem coeff_N_tail (n : ℕ) : PowerSeries.coeff (n + 8) N = 0 := by
  rw [numerator_expansion_C]
  simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

private theorem coeff_N_initial :
    PowerSeries.coeff 0 N = 0 ∧ PowerSeries.coeff 1 N = 1 ∧
    PowerSeries.coeff 2 N = -8 ∧ PowerSeries.coeff 3 N = 24 ∧
    PowerSeries.coeff 4 N = -34 ∧ PowerSeries.coeff 5 N = 24 ∧
    PowerSeries.coeff 6 N = -8 ∧ PowerSeries.coeff 7 N = 1 := by
  rw [numerator_expansion_C]
  norm_num [PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_C_mul_X_pow]

/-- The recurrence-defined sequence has exactly the generating function in formula (2). -/
theorem generating_function_identity :
    PowerSeries.mk (fun n => (a n : ℚ)) * D = N := by
  apply PowerSeries.ext
  intro n
  by_cases hn : 8 ≤ n
  · obtain ⟨m, hm⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    subst n
    rw [coeff_mul_D_tail, coeff_N_tail]
    exact_mod_cast rational_tail_equation m
  · rcases initial_coefficient_equations with ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
    rcases coeff_N_initial with ⟨hN0, hN1, hN2, hN3, hN4, hN5, hN6, hN7⟩
    interval_cases n
    · rw [coeff_mul_D, hN0]; norm_num [lag]; exact_mod_cast ha0
    · rw [coeff_mul_D, hN1]; norm_num [lag]; exact_mod_cast ha1
    · rw [coeff_mul_D, hN2]; norm_num [lag]; exact_mod_cast ha2
    · rw [coeff_mul_D, hN3]; norm_num [lag]; exact_mod_cast ha3
    · rw [coeff_mul_D, hN4]; norm_num [lag]; exact_mod_cast ha4
    · rw [coeff_mul_D, hN5]; norm_num [lag]; exact_mod_cast ha5
    · rw [coeff_mul_D, hN6]; norm_num [lag]; exact_mod_cast ha6
    · rw [coeff_mul_D, hN7]; norm_num [lag]; exact_mod_cast ha7

/-- Division form of the generating function in formula (2). -/
theorem generating_function :
    PowerSeries.mk (fun n => (a n : ℚ)) = N * D⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq]
  · exact generating_function_identity
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, denominator_expansion]
    norm_num [PowerSeries.coeff_X_pow]

/-- Formula (2) uniquely determines the recurrence-defined integer coefficients. -/
theorem coefficients_unique (b : ℕ → ℤ)
    (hb : PowerSeries.mk (fun n => (b n : ℚ)) * D = N) : ∀ n, b n = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let bq : ℕ → ℚ := fun i => b i
      let aq : ℕ → ℚ := fun i => a i
      have hlag (k : ℕ) (hk : 0 < k) : lag bq n k = lag aq n k := by
        simp only [lag, bq, aq]
        split_ifs with hkn
        · rw [ih (n - k) (by omega)]
        · rfl
      have hcoeff :
          bq n - 14 * lag bq n 1 + 75 * lag bq n 2 - 196 * lag bq n 3 +
              269 * lag bq n 4 - 196 * lag bq n 5 + 75 * lag bq n 6 -
                14 * lag bq n 7 + lag bq n 8 =
            aq n - 14 * lag aq n 1 + 75 * lag aq n 2 - 196 * lag aq n 3 +
              269 * lag aq n 4 - 196 * lag aq n 5 + 75 * lag aq n 6 -
                14 * lag aq n 7 + lag aq n 8 := by
        calc
          _ = PowerSeries.coeff n (PowerSeries.mk bq * D) := (coeff_mul_D bq n).symm
          _ = PowerSeries.coeff n N := congrArg (PowerSeries.coeff n) hb
          _ = PowerSeries.coeff n (PowerSeries.mk aq * D) :=
            (congrArg (PowerSeries.coeff n) generating_function_identity).symm
          _ = _ := coeff_mul_D aq n
      rw [hlag 1 (by omega), hlag 2 (by omega), hlag 3 (by omega),
        hlag 4 (by omega), hlag 5 (by omega), hlag 6 (by omega),
        hlag 7 (by omega), hlag 8 (by omega)] at hcoeff
      have hcast : (b n : ℚ) = (a n : ℚ) := by
        change bq n = aq n
        linear_combination hcoeff
      exact_mod_cast hcast

/-- In characteristic two, the order-eight recurrence keeps only the even lags. -/
theorem reduced_recurrence (n : Nat) :
    (a (n + 8) : ZMod 2) =
      (a n : ZMod 2) + a (n + 2) + a (n + 4) + a (n + 6) := by
  have h := congrArg (fun z : Int => (z : ZMod 2)) (a_recurrence n)
  push_cast at h
  have h' : (a (n + 8) : ZMod 2) =
      (a (n + 6) : ZMod 2) + a (n + 4) + a (n + 2) + a n := by
    simpa [show (14 : ZMod 2) = 0 by decide,
      show (75 : ZMod 2) = 1 by decide,
      show (196 : ZMod 2) = 0 by decide,
      show (269 : ZMod 2) = 1 by decide,
      sub_eq_add_neg, CharTwo.neg_eq, Nat.add_assoc] using h
  calc
    (a (n + 8) : ZMod 2) =
        (a (n + 6) : ZMod 2) + a (n + 4) + a (n + 2) + a n := h'
    _ = (a n : ZMod 2) + a (n + 2) + a (n + 4) + a (n + 6) := by ac_rfl

/-- Two shifted reduced recurrences cancel in characteristic two, forcing period ten. -/
theorem parity_period_ten : Function.Periodic (fun n => (a n : ZMod 2)) 10 := by
  intro n
  have h0 := reduced_recurrence n
  have h2 := reduced_recurrence (n + 2)
  norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h2
  calc
    (a (n + 10) : ZMod 2) =
        (a (n + 2) : ZMod 2) + a (n + 4) + a (n + 6) + a (n + 8) := h2
    _ = (a n : ZMod 2) := by
      rw [h0]
      linear_combination CharTwo.add_self_eq_zero (a (n + 2) : ZMod 2) +
        CharTwo.add_self_eq_zero (a (n + 4) : ZMod 2) +
        CharTwo.add_self_eq_zero (a (n + 6) : ZMod 2)

private theorem initial_parities (i : Fin 10) :
    (a i : ZMod 2) = (![0, 1, 0, 1, 0, 0, 0, 1, 0, 1] : Fin 10 -> ZMod 2) i := by
  fin_cases i <;>
    simp only [a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven,
      a_eight, a_nine] <;> decide

private theorem initial_parity_characterization (i : Fin 10) :
    ((a i : ZMod 2) = 1) ↔ i.val ∈ ({1, 3, 7, 9} : Finset Nat) := by
  rw [initial_parities]
  fin_cases i <;> decide

/-- For A396093, odd values occur exactly in residues 1, 3, 7, and 9 modulo ten. -/
theorem odd_iff_mod_ten (n : Nat) :
    Odd (a n) ↔ n % 10 ∈ ({1, 3, 7, 9} : Finset Nat) := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hperiod := parity_period_ten.map_mod_nat n
  rw [← hperiod]
  let i : Fin 10 := ⟨n % 10, Nat.mod_lt n (by decide)⟩
  simpa [i] using initial_parity_characterization i

/-- The covered parity theorem for every integer sequence defined by formula (2). -/
theorem odd_iff_mod_ten_of_generating_function (b : ℕ → ℤ)
    (hb : PowerSeries.mk (fun n => (b n : ℚ)) * D = N) (n : ℕ) :
    Odd (b n) ↔ n % 10 ∈ ({1, 3, 7, 9} : Finset ℕ) := by
  rw [coefficients_unique b hb n]
  exact odd_iff_mod_ten n

/-- OEIS conjecture 1: `a(2*n) is even for n >= 1`. -/
theorem even_at_even_index (n : Nat) (_hn : 1 <= n) : Even (a (2 * n)) := by
  rw [← Int.not_odd_iff_even]
  rw [odd_iff_mod_ten]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- OEIS conjecture 2: `a(2*n-1) is even iff n=5*k-2` for some `k >= 1`. -/
theorem even_at_odd_index_iff (n : Nat) (hn : 1 <= n) :
    Even (a (2 * n - 1)) ↔ ∃ k : Nat, 1 <= k ∧ n = 5 * k - 2 := by
  rw [← Int.not_odd_iff_even]
  rw [odd_iff_mod_ten]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hmod : n % 5 = 3 := by omega
    have hdiv := Nat.mod_add_div n 5
    refine ⟨n / 5 + 1, by omega, ?_⟩
    omega
  · rintro ⟨k, hk, rfl⟩
    omega

/-- OEIS conjecture 1 for every integer sequence defined by formula (2). -/
theorem even_at_even_index_of_generating_function (b : ℕ → ℤ)
    (hb : PowerSeries.mk (fun n => (b n : ℚ)) * D = N)
    (n : ℕ) (hn : 1 ≤ n) : Even (b (2 * n)) := by
  rw [coefficients_unique b hb (2 * n)]
  exact even_at_even_index n hn

/-- OEIS conjecture 2 for every integer sequence defined by formula (2). -/
theorem even_at_odd_index_iff_of_generating_function (b : ℕ → ℤ)
    (hb : PowerSeries.mk (fun n => (b n : ℚ)) * D = N)
    (n : ℕ) (hn : 1 ≤ n) :
    Even (b (2 * n - 1)) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 5 * k - 2 := by
  rw [coefficients_unique b hb (2 * n - 1)]
  exact even_at_odd_index_iff n hn

/-- The basic rational map in the OEIS definition, over the rational-function field. -/
def Bf (y : RatFunc ℚ) : RatFunc ℚ := y / (1 - y) ^ 2

/-- Formula (2) is unconditionally the third iterate of `Bf` in `ℚ(x)`. -/
private theorem triple_B_eq_formula_two :
    Bf (Bf (Bf RatFunc.X)) =
      (RatFunc.X * (1 - RatFunc.X) ^ 2 *
          (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2) /
        (1 - 7 * RatFunc.X + 13 * RatFunc.X ^ 2 - 7 * RatFunc.X ^ 3 +
          RatFunc.X ^ 4) ^ 2 := by
  have polynomial_ne_zero_of_constant_one (p : Polynomial ℚ)
      (hp : p.coeff 0 = 1) : p ≠ 0 := by
    intro h
    rw [h] at hp
    norm_num at hp
  have hpPoly : (1 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
    apply polynomial_ne_zero_of_constant_one
    norm_num
  have hqPoly :
      (1 - 3 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ≠ 0 := by
    apply polynomial_ne_zero_of_constant_one
    norm_num [Polynomial.coeff_X_pow]
  have hrPoly :
      (1 - 7 * Polynomial.X + 13 * Polynomial.X ^ 2 - 7 * Polynomial.X ^ 3 +
        Polynomial.X ^ 4 : Polynomial ℚ) ≠ 0 := by
    apply polynomial_ne_zero_of_constant_one
    norm_num [Polynomial.coeff_X_pow]
  have hp : (1 - RatFunc.X : RatFunc ℚ) ≠ 0 := by
    simpa only [map_sub, map_one, RatFunc.algebraMap_X] using
      RatFunc.algebraMap_ne_zero hpPoly
  have hq :
      (1 - 3 * RatFunc.X + RatFunc.X ^ 2 : RatFunc ℚ) ≠ 0 := by
    simpa only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat,
      RatFunc.algebraMap_X] using RatFunc.algebraMap_ne_zero hqPoly
  have hr :
      (1 - 7 * RatFunc.X + 13 * RatFunc.X ^ 2 - 7 * RatFunc.X ^ 3 +
        RatFunc.X ^ 4 : RatFunc ℚ) ≠ 0 := by
    simpa only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat,
      RatFunc.algebraMap_X] using RatFunc.algebraMap_ne_zero hrPoly
  have one_sub_B :
      1 - Bf RatFunc.X =
        (1 - 3 * RatFunc.X + RatFunc.X ^ 2) / (1 - RatFunc.X) ^ 2 := by
    simp only [Bf]
    field_simp [hp]
    ring
  have B_comp_two :
      Bf (Bf RatFunc.X) =
        RatFunc.X * (1 - RatFunc.X) ^ 2 /
          (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 := by
    rw [Bf, one_sub_B]
    simp only [Bf]
    field_simp [hp, hq]
  have one_sub_B_comp_two :
      1 - Bf (Bf RatFunc.X) =
        (1 - 7 * RatFunc.X + 13 * RatFunc.X ^ 2 - 7 * RatFunc.X ^ 3 +
            RatFunc.X ^ 4) /
          (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 := by
    rw [B_comp_two]
    have hq2 : (1 - 3 * RatFunc.X + RatFunc.X ^ 2 : RatFunc ℚ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 hq
    calc
      (1 : RatFunc ℚ) - RatFunc.X * (1 - RatFunc.X) ^ 2 /
          (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 =
          (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 /
              (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 -
            RatFunc.X * (1 - RatFunc.X) ^ 2 /
              (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 := by
        rw [div_self hq2]
      _ = ((1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 -
              RatFunc.X * (1 - RatFunc.X) ^ 2) /
            (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 := by
        rw [sub_div]
      _ = (1 - 7 * RatFunc.X + 13 * RatFunc.X ^ 2 - 7 * RatFunc.X ^ 3 +
              RatFunc.X ^ 4) /
            (1 - 3 * RatFunc.X + RatFunc.X ^ 2) ^ 2 := by
        congr 1
        ring_nf
  rw [Bf, one_sub_B_comp_two, B_comp_two]
  field_simp [hp, hq, hr]

-- Fidelity witnesses: every quantified domain is inhabited.
example : Nat := 0
example : Int := 0
example : PowerSeries ℚ := 0
example : RatFunc ℚ := 0
example : ∃ n : Nat, 1 <= n := ⟨1, by decide⟩

#print axioms denominator_expansion
#print axioms numerator_expansion
#print axioms rational_tail_equation
#print axioms initial_coefficient_equations
#print axioms generating_function_identity
#print axioms generating_function
#print axioms coefficients_unique
#print axioms reduced_recurrence
#print axioms parity_period_ten
#print axioms odd_iff_mod_ten
#print axioms odd_iff_mod_ten_of_generating_function
#print axioms even_at_even_index
#print axioms even_at_odd_index_iff
#print axioms even_at_even_index_of_generating_function
#print axioms even_at_odd_index_iff_of_generating_function
#print axioms triple_B_eq_formula_two

end


end D5.S3.Arith.RationalCompositionParityPeriodTen
