/- GID: D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/PositiveNewtonSums
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Strict positive monomial coefficients of the five-data Newton sums. -/

/-
result:
  proof_shape: content
  escape_witness: the all-degree multinomial logarithm bridges and
    positive_series_bridge derive the strict-positive coefficient series.
  admission_basis: open-problem-resolution (#23723; Proved)
  Direct frozen dependencies: none (Mathlib imports only).
  Unfinished four-slot registration: https://github.com/the-omega-institute/trureturing/issues/23747
  Reg binding: declared_unresolved; IE-C050 ClosedTruthReadout,
    source.residual_requires_open. No declared_validated claim.
-/

import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-! # Positive monomial coefficients of normalized Newton sums -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open Finset PowerSeries

namespace D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums

/-- Five multiplicities, corresponding to weights one through five. -/
abbrev Multiplicity := Fin 5 → ℕ

/-- The number of factors in a monomial. -/
def count (m : Multiplicity) : ℕ := ∑ i, m i

/-- The weighted degree of a monomial. -/
def degree (m : Multiplicity) : ℕ := ∑ i, (i.val + 1) * m i

private lemma count_le_degree (m : Multiplicity) : count m ≤ degree m := by
  apply Finset.sum_le_sum
  intro i _
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- All multiplicity vectors of the given weighted degree, each occurring once. -/
def multiplicities (k : ℕ) : Finset Multiplicity :=
  (range (k + 1)).biUnion fun r => (piAntidiag univ r).filter fun m => degree m = k

private lemma mem_multiplicities (k : ℕ) (m : Multiplicity) :
    m ∈ multiplicities k ↔ degree m = k := by
  simp only [multiplicities, mem_biUnion, mem_range, mem_filter, mem_piAntidiag,
    mem_univ, implies_true, and_true]
  constructor
  · rintro ⟨r, _, _, h⟩; exact h
  · intro h
    exact ⟨count m, by have := count_le_degree m; omega, rfl, h⟩

/-- The coefficient of a single monomial before any data valuation. -/
def literalCoefficient (k : ℕ+) (m : Multiplicity) : ℚ :=
  ((k : ℕ) : ℚ) / (5 * (count m : ℚ)) * (-1) ^ ((k : ℕ) + count m) *
    (((count m).factorial : ℚ) / (∏ i, ((m i).factorial : ℚ))) *
      ∏ i, ((5 : ℕ).choose (i.val + 1) : ℚ) ^ m i

/-- The unsigned coefficient of the same monomial. -/
def unsignedCoefficient (k : ℕ+) (m : Multiplicity) : ℚ :=
  ((k : ℕ) : ℚ) / (5 * (count m : ℚ)) *
    (((count m).factorial : ℚ) / (∏ i, ((m i).factorial : ℚ))) *
      ∏ i, ((5 : ℕ).choose (i.val + 1) : ℚ) ^ m i

/-- A301420, defined only at positive indices by strict positivity of each monomial. -/
def positiveCoefficient (k : ℕ+) : ℚ :=
  ∑ m ∈ multiplicities k, if 0 < literalCoefficient k m then literalCoefficient k m else 0

/-- The shifted series has coefficient a(n+1) at degree n. -/
def positiveSeries : ℚ⟦X⟧ := mk fun n => positiveCoefficient ⟨n + 1, by omega⟩

private lemma literal_eq_sign_mul (k : ℕ+) (m : Multiplicity) :
    literalCoefficient k m = (-1 : ℚ) ^ ((k : ℕ) + count m) * unsignedCoefficient k m := by
  unfold literalCoefficient unsignedCoefficient
  ring

private lemma unsigned_nonneg (k : ℕ+) (m : Multiplicity) :
    0 ≤ unsignedCoefficient k m := by
  unfold unsignedCoefficient
  positivity

private lemma abs_literal (k : ℕ+) (m : Multiplicity) :
    |literalCoefficient k m| = unsignedCoefficient k m := by
  rw [literal_eq_sign_mul, abs_mul, abs_pow]
  norm_num [abs_of_nonneg (unsigned_nonneg k m)]

private lemma twice_positive_part (x : ℚ) :
    2 * (if 0 < x then x else 0) = |x| + x := by
  split_ifs with h
  · rw [abs_of_pos h]; ring
  · rw [abs_of_nonpos (le_of_not_gt h)]; ring

private lemma split_positive (k : ℕ+) :
    2 * positiveCoefficient k =
      (∑ m ∈ multiplicities k, unsignedCoefficient k m) +
      ∑ m ∈ multiplicities k, literalCoefficient k m := by
  simp only [positiveCoefficient, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  rw [twice_positive_part, abs_literal]

private lemma factorial_quotient (m : Multiplicity) :
    ((count m).factorial : ℚ) / (∏ i, ((m i).factorial : ℚ)) =
      (Nat.multinomial univ m : ℚ) := by
  have h := Nat.multinomial_spec univ m
  have hp : (∏ i, ((m i).factorial : ℚ)) ≠ 0 := by positivity
  apply (div_eq_iff hp).mpr
  simpa only [count, mul_comm] using (show ((∑ i, m i).factorial : ℚ) =
    (∏ i, ((m i).factorial : ℚ)) * (Nat.multinomial univ m : ℚ) by exact_mod_cast h.symm)

private lemma coefficient_power (w : Fin 5 → ℚ) (r k : ℕ) :
    coeff k ((∑ i, monomial (i.val + 1) (w i) : ℚ⟦X⟧) ^ r) =
      ∑ m ∈ piAntidiag univ r,
        if degree m = k then
          (Nat.multinomial univ m : ℚ) * ∏ i, (w i) ^ m i else 0 := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  simp only [map_sum, monomial_pow, prod_monomial, coeff_natCast_mul,
    coeff_monomial]
  apply sum_congr rfl
  intro m _
  have hd : (∑ i, m i * (i.val + 1)) = degree m := by
    simp [degree, Nat.mul_comm]
  rw [hd]
  by_cases h : degree m = k
  · simp only [h, ite_true]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]

private lemma sum_by_count (k : ℕ) (f : Multiplicity → ℚ) :
    (∑ m ∈ multiplicities k, f m) =
      ∑ r ∈ range (k + 1), ∑ m ∈ piAntidiag univ r,
        if degree m = k then f m else 0 := by
  calc
    _ = ∑ m ∈ multiplicities k, if degree m = k then f m else 0 := by
      apply sum_congr rfl
      intro m hm
      rw [ite_eq_left ((mem_multiplicities k m).mp hm)]
    _ = _ := by
      unfold multiplicities
      rw [Finset.sum_biUnion]
      · simp only [Finset.sum_filter]
        apply sum_congr rfl
        intro r _
        apply sum_congr rfl
        intro m _
        split_ifs <;> rfl
      · intro r hr s hs hrs
        apply Finset.disjoint_left.mpr
        intro m hm hn
        have hm' := (mem_piAntidiag.mp (mem_filter.mp hm).1).1
        have hn' := (mem_piAntidiag.mp (mem_filter.mp hn).1).1
        exact hrs (hm'.symm.trans hn')
private lemma log_coeff_finite (p : ℚ⟦X⟧) (hp : constantCoeff p = 0) (k : ℕ) :
    coeff k ((PowerSeries.log ℚ).subst p) =
      ∑ r ∈ range (k + 1),
        (if r = 0 then 0 else (-1 : ℚ) ^ (r + 1) / r) * coeff k (p ^ r) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hp)]
  rw [finsum_eq_sum_of_support_subset (s := range (k + 1))]
  · simp [coeff_log, smul_eq_mul]
  · intro r hr
    apply mem_range.mpr
    by_contra h
    have hkr : k < r := by omega
    have hz : coeff k (p ^ r) = 0 := by
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast hkr)
        (le_order_pow_of_constantCoeff_eq_zero r hp)
    exact hr (by simp [hz])

/-- The binomial data polynomial, with zero constant coefficient. -/
def dataSeries : ℚ⟦X⟧ := ∑ i : Fin 5, monomial (i.val + 1) ((5 : ℕ).choose (i.val + 1) : ℚ)

private lemma dataSeries_constant : constantCoeff dataSeries = 0 := by
  simp [dataSeries, ← coeff_zero_eq_constantCoeff, coeff_monomial]

private lemma unsigned_sum (k : ℕ+) :
    (∑ m ∈ multiplicities k, unsignedCoefficient k m) =
      ∑ r ∈ range ((k : ℕ) + 1),
        ((k : ℕ) : ℚ) / (5 * r) * coeff k (dataSeries ^ r) := by
  rw [sum_by_count]
  apply sum_congr rfl
  intro r _
  rw [dataSeries, coefficient_power, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hc : count m = r := (mem_piAntidiag.mp hm).1
  by_cases hd : degree m = (k : ℕ)
  · simp only [hd, ite_true, unsignedCoefficient]
    rw [factorial_quotient, hc]
    ring
  · simp only [hd, ite_false, mul_zero]

private lemma signed_sum (k : ℕ+) :
    (∑ m ∈ multiplicities k, literalCoefficient k m) =
      ∑ r ∈ range ((k : ℕ) + 1),
        (-1 : ℚ) ^ ((k : ℕ) + r) * ((k : ℕ) : ℚ) / (5 * r) *
          coeff k (dataSeries ^ r) := by
  rw [sum_by_count]
  apply sum_congr rfl
  intro r _
  rw [dataSeries, coefficient_power, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hc : count m = r := (mem_piAntidiag.mp hm).1
  by_cases hd : degree m = (k : ℕ)
  · simp only [hd, ite_true, literal_eq_sign_mul, unsignedCoefficient]
    rw [factorial_quotient, hc]
    ring
  · simp only [hd, ite_false, mul_zero]

private lemma coeff_neg_power (p : ℚ⟦X⟧) (r k : ℕ) :
    coeff k ((-p) ^ r) = (-1 : ℚ) ^ r * coeff k (p ^ r) := by
  rw [show -p = C (-1) * p by simp, mul_pow, ← map_pow, coeff_C_mul]

/-- The unsigned logarithmic aggregate. -/
def unsignedLog : ℚ⟦X⟧ := -(C (1 / 5) * (PowerSeries.log ℚ).subst (-dataSeries))

/-- The signed logarithmic aggregate. -/
def signedLog : ℚ⟦X⟧ :=
  -(C (1 / 5) * (PowerSeries.log ℚ).subst (rescale (-1) dataSeries))

private lemma unsigned_log_bridge (k : ℕ+) :
    ((k : ℕ) : ℚ) * coeff k unsignedLog =
      ∑ m ∈ multiplicities k, unsignedCoefficient k m := by
  rw [unsigned_sum, unsignedLog, map_neg, coeff_C_mul,
    log_coeff_finite _ (by simp [dataSeries_constant]), ← neg_mul, mul_sum, mul_sum]
  apply sum_congr rfl
  intro r _
  rw [coeff_neg_power]
  by_cases hr : r = 0
  · subst r; simp
  · rw [ite_eq_right hr, pow_succ]
    have hs : (-1 : ℚ) ^ r * (-1 : ℚ) ^ r = 1 := by
      rw [← mul_pow]; norm_num
    calc
      _ = (((k : ℕ) : ℚ) / (5 * r) * coeff k (dataSeries ^ r)) *
        ((-1 : ℚ) ^ r * (-1 : ℚ) ^ r) := by ring
      _ = _ := by rw [hs, mul_one]

private lemma signed_log_bridge (k : ℕ+) :
    ((k : ℕ) : ℚ) * coeff k signedLog =
      ∑ m ∈ multiplicities k, literalCoefficient k m := by
  rw [signed_sum, signedLog, map_neg, coeff_C_mul,
    log_coeff_finite _ (by
      rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
      simp only [pow_zero, one_mul, coeff_zero_eq_constantCoeff, dataSeries_constant]),
    ← neg_mul, mul_sum, mul_sum]
  apply sum_congr rfl
  intro r _
  rw [← map_pow, coeff_rescale]
  by_cases hr : r = 0
  · subst r; simp
  · rw [ite_eq_right hr, pow_succ, pow_add]
    ring

private lemma positive_series_bridge :
    positiveSeries = C (1 / 2) * (PowerSeries.derivative unsignedLog + PowerSeries.derivative signedLog) := by
  ext n
  rw [positiveSeries, coeff_mk, coeff_C_mul, map_add, coeff_derivative, coeff_derivative]
  have h := split_positive (⟨n + 1, by omega⟩ : ℕ+)
  rw [← unsigned_log_bridge (⟨n + 1, by omega⟩ : ℕ+),
    ← signed_log_bridge (⟨n + 1, by omega⟩ : ℕ+)] at h
  change 2 * positiveCoefficient ⟨n + 1, _⟩ =
    ((n + 1 : ℕ) : ℚ) * coeff (n + 1) unsignedLog +
    ((n + 1 : ℕ) : ℚ) * coeff (n + 1) signedLog at h
  push_cast at h
  linear_combination h / 2

private lemma monomial_as (n : ℕ) (c : ℚ) :
    monomial n c = C c * (X : ℚ⟦X⟧) ^ n := by
  rw [X_pow_eq, ← monomial_zero_eq_C_apply, monomial_mul_monomial]
  simp

private lemma dataSeries_eq : dataSeries = (1 + X) ^ 5 - 1 := by
  norm_num [dataSeries, Fin.sum_univ_succ, monomial_as, Nat.choose]
  ring

private lemma signed_dataSeries_eq : rescale (-1) dataSeries = (1 - X) ^ 5 - 1 := by
  rw [dataSeries_eq, map_sub, map_pow, map_add, map_one, rescale_X]
  simp only [map_neg, map_one, neg_one_mul, sub_eq_add_neg]

private lemma logarithmic_derivative (p : ℚ⟦X⟧) (hp : constantCoeff p = 0) :
    PowerSeries.derivative ((PowerSeries.log ℚ).subst p) * (1 + p) =
      PowerSeries.derivative p := by
  let hs := HasSubst.of_constantCoeff_zero' hp
  have h := congrArg (fun f : ℚ⟦X⟧ => f.subst p)
    (derivative_log_mul_one_add_X (A := ℚ))
  rw [← coe_substAlgHom hs] at h
  simp only [map_mul, map_add, map_one, substAlgHom_X] at h
  rw [derivative_subst hs]
  calc
    _ = (PowerSeries.derivative p) *
      ((PowerSeries.derivative (PowerSeries.log ℚ)).subst p * (1 + p)) := by ring
    _ = _ := by rw [← coe_substAlgHom hs, h, mul_one]

private lemma rational_constant_cancel (n : ℕ) (hn : n ≠ 0) :
    C (1 / (n : ℚ)) * (n : ℚ⟦X⟧) = 1 := by
  rw [show (n : ℚ⟦X⟧) = C (n : ℚ) by simp, ← map_mul]
  simp [hn]

private lemma unsigned_derivative :
    PowerSeries.derivative unsignedLog * (2 - (1 + X) ^ 5) = (1 + X) ^ 4 := by
  have h := logarithmic_derivative (-dataSeries) (by simp [dataSeries_constant])
  rw [dataSeries_eq] at h
  have hd : PowerSeries.derivative (-((1 + X : ℚ⟦X⟧) ^ 5 - 1)) =
      -(5 * (1 + X) ^ 4) := by simp [derivative_pow]
  rw [hd] at h
  simp only [unsignedLog, map_neg, Derivation.leibniz, derivative_C, zero_mul,
    zero_add, smul_eq_mul]
  have he : 1 + (-((1 + X : ℚ⟦X⟧) ^ 5 - 1)) = 2 - (1 + X) ^ 5 := by ring
  rw [he] at h
  rw [← he, ← dataSeries_eq]
  calc
    _ = -(C (1 / 5)) *
      (PowerSeries.derivative ((PowerSeries.log ℚ).subst (-dataSeries)) *
        (1 + -dataSeries)) := by ring
    _ = (C (1 / 5) * 5) * (1 + X) ^ 4 := by rw [dataSeries_eq, he, h]; ring
    _ = _ := by
      have h5 := rational_constant_cancel 5 (by norm_num)
      norm_num only [Nat.cast_ofNat] at h5
      rw [h5, one_mul]

private lemma signed_derivative :
    PowerSeries.derivative signedLog * (1 - X) = 1 := by
  have hp : constantCoeff (rescale (-1) dataSeries) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
    simp [dataSeries_constant]
  have h := logarithmic_derivative (rescale (-1) dataSeries) hp
  rw [signed_dataSeries_eq] at h
  have hd : PowerSeries.derivative ((1 - X : ℚ⟦X⟧) ^ 5 - 1) =
      -(5 * (1 - X) ^ 4) := by simp [derivative_pow]
  rw [hd] at h
  have hc : (1 - X : ℚ⟦X⟧) ^ 4 ≠ 0 := by
    apply pow_ne_zero
    intro he
    have := congrArg (constantCoeff (R := ℚ)) he
    norm_num at this
  apply mul_right_cancel₀ hc
  simp only [signedLog, map_neg, Derivation.leibniz, derivative_C, zero_mul,
    zero_add, smul_eq_mul, one_mul]
  rw [signed_dataSeries_eq]
  have he : (1 + ((1 - X : ℚ⟦X⟧) ^ 5 - 1)) = (1 - X) ^ 5 := by ring
  rw [he] at h
  calc
    _ = -(C (1 / 5) : ℚ⟦X⟧) *
      (PowerSeries.derivative ((PowerSeries.log ℚ).subst ((1 - X) ^ 5 - 1)) *
        (1 - X) ^ 5) := by ring
    _ = (C (1 / 5) * 5) * (1 - X) ^ 4 := by rw [h]; ring
    _ = _ := by
      have h5 := rational_constant_cancel 5 (by norm_num)
      norm_num only [Nat.cast_ofNat] at h5
      rw [h5, one_mul]

private lemma rational_equation :
    positiveSeries * ((1 - X) * (2 - (1 + X) ^ 5)) = 1 - X * (1 + X) ^ 4 := by
  rw [positive_series_bridge]
  calc
    _ = C (1 / 2) *
      ((PowerSeries.derivative unsignedLog * (2 - (1 + X) ^ 5)) * (1 - X) +
       (PowerSeries.derivative signedLog * (1 - X)) * (2 - (1 + X) ^ 5)) := by ring
    _ = (C (1 / 2) * 2) * (1 - X * (1 + X) ^ 4) := by
      rw [unsigned_derivative, signed_derivative]; ring
    _ = _ := by
      have h2 := rational_constant_cancel 2 (by norm_num)
      norm_num only [Nat.cast_ofNat] at h2
      rw [h2, one_mul]

/-- The exact order-fourteen relation on the positive-index domain. -/
def recurrence (a : ℕ+ → ℚ) : Prop :=
  ∀ n : ℕ+, a (n + 14) = 7 * a (n + 13) - a (n + 12) - 6 * a (n + 11) +
    2 * a (n + 10) - a (n + 9) + 4 * a (n + 8) + a (n + 7) +
    4 * a (n + 5) + 2 * a (n + 4) - a (n + 3) - 5 * a (n + 2) -
    4 * a (n + 1) - a n

private def annihilator : ℚ⟦X⟧ :=
  1 - 7 * X + X ^ 2 + 6 * X ^ 3 - 2 * X ^ 4 + X ^ 5 - 4 * X ^ 6 - X ^ 7 -
    4 * X ^ 9 - 2 * X ^ 10 + X ^ 11 + 5 * X ^ 12 + 4 * X ^ 13 + X ^ 14

private def multiplier : ℚ⟦X⟧ := 1 - X + X ^ 3 - X ^ 4 + X ^ 5 + X ^ 8

private lemma annihilator_factorization :
    annihilator = ((1 - X) * (2 - (1 + X) ^ 5)) * multiplier := by
  unfold annihilator multiplier
  ring

private lemma annihilated :
    annihilator * positiveSeries = (1 - X * (1 + X) ^ 4) * multiplier := by
  rw [annihilator_factorization]
  calc
    _ = (positiveSeries * ((1 - X) * (2 - (1 + X) ^ 5))) * multiplier := by ring
    _ = _ := by rw [rational_equation]

private lemma coeff_positiveSeries (n : ℕ) :
    coeff n positiveSeries = positiveCoefficient ⟨n + 1, by omega⟩ := coeff_mk _ _

private lemma recurrence_proof : recurrence positiveCoefficient := by
  intro n
  have hn := n.pos
  have h := congrArg (coeff ((n : ℕ) + 13)) annihilated
  have hz : coeff ((n : ℕ) + 13) ((1 - X * (1 + X : ℚ⟦X⟧) ^ 4) * multiplier) = 0 := by
    unfold multiplier
    ring_nf
    simp (disch := omega) only [map_add, map_sub, map_neg, coeff_mul_ofNat,
      coeff_mul_natCast, coeff_ofNat_mul, coeff_natCast_mul, coeff_X_pow, coeff_X,
      coeff_one, ite_eq_right, mul_zero, zero_mul, sub_zero, neg_zero, zero_add, sub_self]
  rw [hz] at h
  unfold annihilator at h
  simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_ofNat_mul, coeff_natCast_mul] at h
  have hx : (X : ℚ⟦X⟧) = X ^ 1 := by simp
  rw [hx] at h
  simp only [← pow_mul, Nat.one_mul] at h
  simp (disch := omega) only [coeff_X_pow_mul', ite_eq_left,
    coeff_positiveSeries] at h
  have hi (i : ℕ) (hi : i ≤ 14) : (n : ℕ) + 13 - i + 1 = (n : ℕ) + (14 - i) := by
    omega
  simp only [hi 1 (by omega), hi 2 (by omega), hi 3 (by omega), hi 4 (by omega),
    hi 5 (by omega), hi 6 (by omega), hi 7 (by omega), hi 9 (by omega),
    hi 10 (by omega), hi 11 (by omega), hi 12 (by omega), hi 13 (by omega),
    hi 14 (by omega)] at h
  simp only [Nat.reduceSub, Nat.add_zero,
    show (n : ℕ) + 13 + 1 = (n : ℕ) + 14 by omega] at h
  have he (j : ℕ+) :
      positiveCoefficient ⟨(n : ℕ) + (j : ℕ), by omega⟩ = positiveCoefficient (n + j) := by
    congr 1
  have he0 : positiveCoefficient ⟨(n : ℕ), hn⟩ = positiveCoefficient n := by
    congr 1
  have he1 := he 1
  have he2 := he 2
  have he3 := he 3
  have he4 := he 4
  have he5 := he 5
  have he7 := he 7
  have he8 := he 8
  have he9 := he 9
  have he10 := he 10
  have he11 := he 11
  have he12 := he 12
  have he13 := he 13
  have he14 := he 14
  norm_num only [PNat.val_ofNat] at he1 he2 he3 he4 he5 he7 he8 he9 he10 he11 he12 he13 he14
  rw [he0, he1, he2, he3, he4, he5, he7, he8, he9, he10, he11, he12, he13, he14] at h
  linear_combination h

/-- The literal strict-positive sequence has the shifted generating function and recurrence. -/
theorem result :
    positiveSeries = (1 - X * (1 + X) ^ 4) *
      (((1 - X) * (2 - (1 + X) ^ 5)) : ℚ⟦X⟧)⁻¹ ∧
      recurrence positiveCoefficient := by
  constructor
  · apply (eq_mul_inv_iff_mul_eq (by
    norm_num [map_ofNat])).mpr
    exact rational_equation
  · exact recurrence_proof

#print axioms result

end D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums
