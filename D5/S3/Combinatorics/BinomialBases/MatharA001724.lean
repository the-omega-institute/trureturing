/- GID: D5/S3/Combinatorics/BinomialBases/MatharA001724
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MatharA001724
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The literal signed Stirling sum A001724 satisfies Mathar's five-lag recurrence and its ordinary rational formal series has a nonzero homogeneous differential annihilator. -/

import D5.S3.Combinatorics.BinomialBases.MatharA001722

open scoped BigOperators
namespace D5.S3.Combinatorics.BinomialBases.MatharA001724
open Polynomial

open D5.S3.Combinatorics.BinomialBases.MatharA001722 (falling s falling_degree)

/-- Crstici's inclusive signed sum; no recurrence is assumed. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (n + k) * ((k + 4).choose 4 : ℤ) * (5 : ℤ) ^ k * s (n + 4) (k + 4)

/-- Ordinary rational formal generating series. -/
noncomputable def O : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))

private noncomputable def D : PowerSeries ℚ → PowerSeries ℚ := PowerSeries.derivative

private def Recurrence : Prop := ∀ n : ℕ, 5 ≤ n →
  a n + 5 * (-(n : ℤ) - 6) * a (n - 1) +
    5 * (2 * (n : ℤ)^2 + 22 * (n : ℤ) + 61) * a (n - 2) -
    5 * ((n : ℤ) + 5) * (2 * (n : ℤ)^2 + 20 * (n : ℤ) + 51) * a (n - 3) +
    (5 * (n : ℤ)^4 + 90 * (n : ℤ)^3 + 610 * (n : ℤ)^2 +
      1845 * (n : ℤ) + 2101) * a (n - 4) -
    ((n : ℤ) + 4)^5 * a (n - 5) = 0

private def DFinite (Y : PowerSeries ℚ) : Prop := ∃ (r : ℕ) (p : ℕ → Polynomial ℚ),
  (∃ j : ℕ, j ≤ r ∧ p j ≠ 0) ∧
  (∑ j ∈ Finset.range (r + 1), (p j : PowerSeries ℚ) * (D^[j]) Y) = 0

/-- Mathar's recurrence together with the ordinary-series reading of D-finiteness. -/
def claim : Prop := Recurrence ∧ DFinite O

private noncomputable def shifted (n : ℕ) : Polynomial ℤ :=
  C ((-1 : ℤ)^n) * taylor (-5) (falling (n + 4))

private theorem shifted_coeff (n : ℕ) : (shifted n).coeff 4 = a n := by
  have hd : (hasseDeriv 4 (falling (n+4))).natDegree < n+1 := by
    have h := Polynomial.natDegree_hasseDeriv_le (falling (n+4)) 4
    have h' := falling_degree (n+4)
    omega
  rw [shifted, coeff_C_mul, taylor_coeff, eval_eq_sum_range' hd, Finset.mul_sum, a]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hasseDeriv_coeff]
  simp only [s]
  rw [show (-5 : ℤ) = (-1) * 5 by norm_num, mul_pow, pow_add]
  ring

private theorem shifted_step (n : ℕ) :
    shifted (n+1) = shifted n * (C ((n : ℤ)+9) - X) := by
  have hf : falling ((n+4)+1) = falling (n+4) * (X - C ((n+4 : ℕ) : ℤ)) := by
    simp only [falling, Finset.prod_range_succ]
  have ht : taylor (-5) (X - C ((n+4 : ℕ) : ℤ)) = X - C ((n : ℤ)+9) := by
    rw [taylor_apply, sub_comp, X_comp, C_comp]
    simp only [Nat.cast_add, Nat.cast_ofNat, C_add, C_neg, C_ofNat]
    ring
  unfold shifted
  rw [show n+1+4 = (n+4)+1 by omega, hf, taylor_mul, ht, pow_succ,
    C_mul, C_neg, C_1]
  ring

private theorem recurrence_forward (m : ℕ) :
    a (m+5) - 5*((m : ℤ)+11)*a (m+4) +
      (10*(m : ℤ)^2+210*(m : ℤ)+1105)*a (m+3) -
      (10*(m : ℤ)^3+300*(m : ℤ)^2+3005*(m : ℤ)+10050)*a (m+2) +
      (5*(m : ℤ)^4+190*(m : ℤ)^3+2710*(m : ℤ)^2+
        17195*(m : ℤ)+40951)*a (m+1) - ((m : ℤ)+9)^5*a m = 0 := by
  have hp : shifted (m+5) - C (5*((m : ℤ)+11))*shifted (m+4) +
      C (10*(m : ℤ)^2+210*(m : ℤ)+1105)*shifted (m+3) -
      C (10*(m : ℤ)^3+300*(m : ℤ)^2+3005*(m : ℤ)+10050)*shifted (m+2) +
      C (5*(m : ℤ)^4+190*(m : ℤ)^3+2710*(m : ℤ)^2+
        17195*(m : ℤ)+40951)*shifted (m+1) -
      C (((m : ℤ)+9)^5)*shifted m = -(X^5 * shifted m) := by
    rw [show m+5 = (m+4)+1 by omega, shifted_step,
      show m+4 = (m+3)+1 by omega, shifted_step,
      show m+3 = (m+2)+1 by omega, shifted_step,
      show m+2 = (m+1)+1 by omega, shifted_step, shifted_step]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_pow,
      map_ofNat, C_1]
    ring
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff 4) hp
  simpa only [coeff_sub, coeff_add, coeff_C_mul, shifted_coeff, coeff_neg,
    coeff_X_pow_mul', show ¬5 ≤ 4 by omega, ite_false, neg_zero] using hc

private theorem recurrence_rational (m : ℕ) :
    (a (m+5) : ℚ) - 5*((m : ℚ)+11)*(a (m+4) : ℚ) +
      (10*(m : ℚ)^2+210*(m : ℚ)+1105)*(a (m+3) : ℚ) -
      (10*(m : ℚ)^3+300*(m : ℚ)^2+3005*(m : ℚ)+10050)*(a (m+2) : ℚ) +
      (5*(m : ℚ)^4+190*(m : ℚ)^3+2710*(m : ℚ)^2+
        17195*(m : ℚ)+40951)*(a (m+1) : ℚ) -
      ((m : ℚ)+9)^5*(a m : ℚ) = 0 := by
  exact_mod_cast recurrence_forward m


private noncomputable def op : ℕ → Polynomial ℚ
  | 0 => -35 + 1130*X - 15480*X^2 + 105124*X^3 - 295245*X^4
  | 1 => 1 - 45*X + 1045*X^2 - 13860*X^3 + 99631*X^4 - 304755*X^5
  | 2 => -5*X^2 + 200*X^3 - 3525*X^4 + 30960*X^5 - 111301*X^6
  | 3 => 10*X^4 - 330*X^5 + 4115*X^6 - 18890*X^7
  | 4 => -10*X^6 + 240*X^7 - 1600*X^8
  | 5 => 5*X^8 - 65*X^9
  | 6 => -X^10
  | _ => 0

private noncomputable def term (d j : ℕ) : PowerSeries ℚ :=
  PowerSeries.X^d * (D^[j]) O

private theorem term_coeff (d j n : ℕ) :
    PowerSeries.coeff n (term d j) =
    if d ≤ n then ((n-d+1).ascFactorial j : ℚ) * (a (n-d+j) : ℚ) else 0 := by
  rw [term, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp [D, PowerSeries.coeff_iterate_derivative, O]

private theorem op_expansion :
    (∑ j ∈ Finset.range 7, (op j : PowerSeries ℚ) * (D^[j]) O) =
    -35*term 0 0 + 1130*term 1 0 - 15480*term 2 0 +
    105124*term 3 0 - 295245*term 4 0 +
    term 0 1 - 45*term 1 1 + 1045*term 2 1 - 13860*term 3 1 +
    99631*term 4 1 - 304755*term 5 1 -
    5*term 2 2 + 200*term 3 2 - 3525*term 4 2 + 30960*term 5 2 -
    111301*term 6 2 + 10*term 4 3 - 330*term 5 3 +
    4115*term 6 3 - 18890*term 7 3 - 10*term 6 4 +
    240*term 7 4 - 1600*term 8 4 + 5*term 8 5 -
    65*term 9 5 - term 10 6 := by
  have cn (n : ℕ) [n.AtLeastTwo] :
      ((ofNat(n) : Polynomial ℚ) : PowerSeries ℚ) = (ofNat(n) : PowerSeries ℚ) :=
    map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, op,
    Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_neg, Polynomial.coe_mul,
    Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_X,
    term, pow_zero, pow_one, one_mul, Function.iterate_zero_apply, Function.iterate_one, cn]
  ring

set_option maxHeartbeats 2000000 in
private theorem annihilates :
    (∑ j ∈ Finset.range 7, (op j : PowerSeries ℚ) * (D^[j]) O) = 0 := by
  rw [op_expansion]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, neg_mul, map_neg, PowerSeries.coeff_ofNat_mul,
    map_zero, term_coeff]
  by_cases hn : n < 10
  · have initial : a 0 = 1 ∧ a 1 = 35 ∧ a 2 = 835 ∧
        a 3 = 17360 ∧ a 4 = 342769 := by
      norm_num [a, s, falling, Finset.sum_range_succ, Finset.prod_range_succ,
        Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one, Nat.choose]
    obtain ⟨h0, h1, h2, h3, h4⟩ := initial
    have hr0 := recurrence_rational 0
    have hr1 := recurrence_rational 1
    have hr2 := recurrence_rational 2
    have hr3 := recurrence_rational 3
    have hr4 := recurrence_rational 4
    have hr5 := recurrence_rational 5
    interval_cases n <;>
      norm_num [Nat.ascFactorial_succ, h0, h1, h2, h3, h4] at *
    all_goals first | linear_combination 5*hr0 | linear_combination 6*hr1 |
      linear_combination 7*hr2 | linear_combination 8*hr3 |
      linear_combination 9*hr4 | linear_combination 10*hr5
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 10 ≤ n by omega)
    rw [show n = m+10 by omega]
    have hr := recurrence_rational (m+6)
    simp (disch := omega) [Nat.add_sub_assoc, Nat.ascFactorial_succ,
      Nat.cast_add, Nat.cast_mul, Nat.add_assoc] at hr ⊢
    linear_combination ((m : ℚ)+11)*hr

/-- The literal all-index recurrence and ordinary-series D-finiteness. -/
theorem result : claim := by
  constructor
  · intro n hn
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [show n = m+5 by omega]
    have h := recurrence_forward m
    convert h using 1
    simp [Nat.add_sub_assoc, Nat.cast_add]
    ring
  · refine ⟨6, op, ⟨6, le_rfl, ?_⟩, annihilates⟩
    simp [op]

end D5.S3.Combinatorics.BinomialBases.MatharA001724
