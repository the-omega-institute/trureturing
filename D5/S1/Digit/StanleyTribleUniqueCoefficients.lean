/- GID: D5/S1/Digit/StanleyTribleUniqueCoefficients
   generality: G
   mirror-B: D5/B/S1/Digit/StanleyTribleUniqueCoefficients
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff]
   utility: none
   digest: Unique coefficients in Stanley's ternary products satisfy a cubic recurrence. -/

/- Library search (2026-09-07): searched D5/S1/Digit and D5/S1 for Stanley,
   430741, representations, carries, and Zeckendorf. Carry and Normalize use
   Fibonacci weights, so their rewriting rules do not apply to these weights.
   Searched pinned Mathlib Polynomial.Coeff, Polynomial.BigOperators, finite
   function counting, and interval sums. We reuse coeff_mul_X_pow' and finite
   sums; no theorem for this coefficient distribution was found. Formalpedia
   was screened externally by the requester. An MO web search returned no
   results in this environment. The proof below uses positive overlapping
   coefficient intervals, rather than a guessed finite multiplicity cutoff.
   Digit contained 23 entries before adding this module (capacity 24).
-/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.StanleyTribleUniqueCoefficients

open Finset Polynomial

noncomputable section

/-- Stanley's weights. -/
def G : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => 2 * G (n + 1) + 2 * G n

/-- The largest represented value, using integer coordinates for translations. -/
def span : ℕ → ℤ
  | 0 => 0
  | n + 1 => span n + 2 * (G n : ℤ)

/-- The multiplicity of an integer, with zero multiplicity outside the support. -/
def multiplicity : ℕ → ℤ → ℕ
  | 0, value => if value = 0 then 1 else 0
  | n + 1, value => multiplicity n value + multiplicity n (value - G n) +
      multiplicity n (value - 2 * G n)

/-- The product in the question, over natural-number coefficients. -/
def product (n : ℕ) : ℕ[X] :=
  ∏ index ∈ range n, (1 + X ^ G index + X ^ (2 * G index))

private theorem weight_pos (n : ℕ) : 0 < G n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n first second => simp only [G]; omega

private theorem weight_double (n : ℕ) : 2 * G n < G (n + 1) := by
  cases n with
  | zero => decide
  | succ n =>
    have := weight_pos n
    simp only [G]
    omega

private theorem bounds (n : ℕ) :
    0 ≤ span n ∧ (G n : ℤ) ≤ span n + 1 ∧ span n < 2 * (G n : ℤ) ∧
      span n < (G (n + 1) : ℤ) ∧
      (G (n + 1) : ℤ) ≤ span n + 2 * G n + 1 := by
  induction n with
  | zero => norm_num [span, G]
  | succ n ih =>
    have positive := weight_pos n
    have nextPositive := weight_pos (n + 1)
    have double := weight_double n
    have recurrenceEq : (G (n + 2) : ℤ) = 2 * (G (n + 1) : ℤ) + 2 * (G n : ℤ) := by
      simp only [G, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    simp only [span, show n + 1 + 1 = n + 2 by omega]
    omega

/-- The exact overlap identity; in particular the overlap is two levels shorter. -/
theorem span_overlap (n : ℕ) : span (n + 2) = (G (n + 2) : ℤ) + span n := by
  simp only [span, G, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- There are no holes in the represented interval. -/
theorem multiplicity_pos (n : ℕ) (value : ℤ) :
    0 < multiplicity n value ↔ 0 ≤ value ∧ value ≤ span n := by
  induction n generalizing value with
  | zero => simp only [multiplicity, span]; split_ifs <;> omega
  | succ n ih =>
    have bound := bounds n
    have positive := weight_pos n
    have first := ih value
    have second := ih (value - G n)
    have third := ih (value - 2 * G n)
    simp only [multiplicity, span]
    omega

private theorem multiplicity_zero (n : ℕ) (value : ℤ)
    (outside : value < 0 ∨ span n < value) : multiplicity n value = 0 := by
  have := multiplicity_pos n value
  omega

/-- Complementing every digit makes the coefficient sequence palindromic. -/
theorem multiplicity_reflect (n : ℕ) (value : ℤ) :
    multiplicity n (span n - value) = multiplicity n value := by
  induction n generalizing value with
  | zero => simp [multiplicity, span, neg_eq_zero]
  | succ n ih =>
    have first : span (n + 1) - value = span n - (value - 2 * G n) := by
      rw [span]; ring
    have second : span (n + 1) - value - G n = span n - (value - G n) := by
      rw [span]; ring
    have third : span (n + 1) - value - 2 * G n = span n - value := by
      rw [span]; ring
    rw [multiplicity, second, third, first, ih, ih, ih, multiplicity]
    omega

private def unique (n : ℕ) (value : ℤ) : ℕ :=
  if multiplicity n value = 1 then 1 else 0

private def tally (n : ℕ) (lower upper : ℤ) : ℕ :=
  ∑ value ∈ Ico lower upper, unique n value

private def total (n : ℕ) : ℕ := tally n 0 (span n + 1)

private def overlap (n : ℕ) : ℕ := tally n 0 (span n - G n + 1)

private theorem unique_reflect (n : ℕ) (value : ℤ) :
    unique n (span n - value) = unique n value := by
  simp only [unique, multiplicity_reflect]

private theorem unique_low (n : ℕ) (value : ℤ) (less : value < G n) :
    unique (n + 1) value = unique n value := by
  have positive := weight_pos n
  have first := multiplicity_zero n (value - G n) (Or.inl (by omega))
  have second := multiplicity_zero n (value - 2 * G n) (Or.inl (by omega))
  simp only [unique, multiplicity, first, second, add_zero]

private theorem unique_overlap (n : ℕ) (value : ℤ)
    (lower : (G n : ℤ) ≤ value) (upper : value ≤ span n) :
    unique (n + 1) value = 0 := by
  have positive := weight_pos n
  have first := (multiplicity_pos n value).mpr (by omega)
  have second := (multiplicity_pos n (value - G n)).mpr (by omega)
  have notOne : multiplicity (n + 1) value ≠ 1 := by rw [multiplicity]; omega
  simp only [unique, if_neg notOne]

private theorem unique_middle (n : ℕ) (value : ℤ)
    (lower : span n < value) (upper : value < 2 * G n) :
    unique (n + 1) value = unique n (value - G n) := by
  have first := multiplicity_zero n value (Or.inr lower)
  have second := multiplicity_zero n (value - 2 * G n) (Or.inl (by omega))
  simp only [unique, multiplicity, first, second, zero_add, add_zero]

private theorem unique_overlap_right (n : ℕ) (value : ℤ)
    (lower : 2 * (G n : ℤ) ≤ value) (upper : value ≤ span n + G n) :
    unique (n + 1) value = 0 := by
  rw [← unique_reflect]
  apply unique_overlap <;> simp only [span] <;> omega

private theorem tally_split (n : ℕ) (lower middle upper : ℤ)
    (first : lower ≤ middle) (second : middle ≤ upper) :
    tally n lower upper = tally n lower middle + tally n middle upper := by
  unfold tally
  rw [← Ico_union_Ico_eq_Ico first second,
    sum_union (Ico_disjoint_Ico_consecutive lower middle upper)]

private theorem tally_reflect (n : ℕ) (lower upper : ℤ) :
    tally n lower upper = tally n (span n + 1 - upper) (span n + 1 - lower) := by
  unfold tally
  apply sum_bij (fun value _ => span n - value)
  · intro value member
    simp only [mem_Ico] at member ⊢
    omega
  · intro first firstMem second secondMem equality
    omega
  · intro value member
    refine ⟨span n - value, ?_, by omega⟩
    simp only [mem_Ico] at member ⊢
    omega
  · intro value member
    exact (unique_reflect n value).symm

private theorem sum_translate (function : ℤ → ℕ) (lower upper shift : ℤ) :
    (∑ value ∈ Ico (lower + shift) (upper + shift), function (value - shift)) =
      ∑ value ∈ Ico lower upper, function value := by
  apply sum_bij (fun value _ => value - shift)
  · intro value member
    simp only [mem_Ico] at member ⊢
    omega
  · intro first firstMem second secondMem equality
    omega
  · intro value member
    refine ⟨value + shift, ?_, by omega⟩
    simp only [mem_Ico] at member ⊢
    omega
  · intro value member
    rfl

private theorem tally_low (n : ℕ) (upper : ℤ) (bound : upper ≤ G n) :
    tally (n + 1) 0 upper = tally n 0 upper := by
  apply sum_congr rfl
  intro value member
  apply unique_low
  have := (mem_Ico.mp member).2
  omega

private theorem tally_overlap (n : ℕ) :
    tally (n + 1) (G n) (span n + 1) = 0 := by
  apply sum_eq_zero
  intro value member
  have := mem_Ico.mp member
  apply unique_overlap <;> omega

private theorem tally_overlap_right (n : ℕ) :
    tally (n + 1) (2 * G n) (span n + G n + 1) = 0 := by
  apply sum_eq_zero
  intro value member
  have := mem_Ico.mp member
  apply unique_overlap_right <;> omega

private theorem tally_middle (n : ℕ) :
    tally (n + 1) (span n + 1) (2 * G n) =
      tally n (span n - G n + 1) (G n) := by
  unfold tally
  calc
    _ = ∑ value ∈ Ico (span n + 1) (2 * (G n : ℤ)), unique n (value - G n) := by
      apply sum_congr rfl
      intro value member
      have := mem_Ico.mp member
      apply unique_middle <;> omega
    _ = _ := by
      have first : span n - G n + 1 + G n = span n + 1 := by ring
      have second : (G n : ℤ) + G n = 2 * G n := by ring
      simpa only [first, second] using
        sum_translate (unique n) (span n - G n + 1) (G n) (G n)

private theorem tally_high (n : ℕ) :
    tally (n + 1) (span n + G n + 1) (span n + 2 * G n + 1) =
      tally n 0 (G n) := by
  rw [tally_reflect]
  have first : span (n + 1) + 1 - (span n + 2 * G n + 1) = 0 := by
    rw [span]; ring
  have second : span (n + 1) + 1 - (span n + G n + 1) = G n := by
    rw [span]; ring
  rw [first, second, tally_low n (G n) le_rfl]

private theorem total_split (n : ℕ) : total n = tally n 0 (G n) + overlap n := by
  have bound := bounds n
  have positive := weight_pos n
  unfold total
  rw [tally_split n 0 (G n) (span n + 1) (by omega) (by omega)]
  congr 1
  rw [tally_reflect]
  simp only [sub_self, overlap]
  congr 1
  ring

private theorem low_split (n : ℕ) :
    tally n 0 (G n) = overlap n + tally n (span n - G n + 1) (G n) := by
  have bound := bounds n
  exact tally_split n 0 (span n - G n + 1) (G n) (by omega) (by omega)

private theorem total_step (n : ℕ) : total (n + 1) + 4 * overlap n = 3 * total n := by
  have bound := bounds n
  have positive := weight_pos n
  have partition : total (n + 1) =
      tally (n + 1) 0 (G n) + tally (n + 1) (G n) (span n + 1) +
      tally (n + 1) (span n + 1) (2 * G n) +
      tally (n + 1) (2 * G n) (span n + G n + 1) +
      tally (n + 1) (span n + G n + 1) (span n + 2 * G n + 1) := by
    unfold total
    rw [span]
    rw [tally_split (n + 1) 0 (span n + G n + 1) _ (by omega) (by omega)]
    rw [tally_split (n + 1) 0 (2 * G n) _ (by omega) (by omega)]
    rw [tally_split (n + 1) 0 (span n + 1) _ (by omega) (by omega)]
    rw [tally_split (n + 1) 0 (G n) _ (by omega) (by omega)]
  rw [tally_low n (G n) le_rfl, tally_overlap, tally_middle,
    tally_overlap_right, tally_high] at partition
  have first := total_split n
  have second := low_split n
  omega

private theorem overlap_step (n : ℕ) : overlap (n + 2) + overlap n = total n := by
  have bound := bounds n
  have positive := weight_pos n
  have cut : span (n + 2) - G (n + 2) + 1 = span n + 1 := by
    rw [span_overlap]; ring
  have equality : overlap (n + 2) = tally n 0 (G n) := by
    unfold overlap
    rw [cut, show n + 2 = (n + 1) + 1 by omega,
      tally_low (n + 1) (span n + 1) (by omega),
      tally_split (n + 1) 0 (G n) (span n + 1) (by omega) (by omega),
      tally_low n (G n) le_rfl, tally_overlap, add_zero]
  rw [equality, ← total_split]

private theorem total_recurrence (n : ℕ) :
    total (n + 3) + total (n + 1) + total n = 3 * total (n + 2) := by
  have first := total_step n
  have second : total (n + 3) + 4 * overlap (n + 2) = 3 * total (n + 2) :=
    total_step (n + 2)
  have third := overlap_step n
  omega

/-- The recursively translated multiplicities are precisely the product's coefficients. -/
theorem multiplicity_eq_coeff (n value : ℕ) :
    multiplicity n value = (product n).coeff value := by
  induction n generalizing value with
  | zero => simp [multiplicity, product, coeff_one]
  | succ n ih =>
    have shift (exponent : ℕ) : multiplicity n ((value : ℤ) - exponent) =
        if exponent ≤ value then (product n).coeff (value - exponent) else 0 := by
      split_ifs with order
      · rw [← Nat.cast_sub order, ih]
      · exact multiplicity_zero n _ (Or.inl (by omega))
    have step : product (n + 1) = product n * (1 + X ^ G n + X ^ (2 * G n)) := by
      simp only [product, prod_range_succ]
    rw [step, mul_add, mul_add, mul_one, coeff_add, coeff_add,
      coeff_mul_X_pow', coeff_mul_X_pow', multiplicity, ih, shift]
    have last := shift (2 * G n)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using congrArg
      (fun term => (product n).coeff value +
        (if G n ≤ value then (product n).coeff (value - G n) else 0) + term) last

/-- The support is exactly the entire interval from zero to twice the sum of weights. -/
theorem product_support (n : ℕ) : (product n).support = range ((span n).toNat + 1) := by
  ext value
  rw [mem_support_iff, mem_range, ← multiplicity_eq_coeff]
  have := multiplicity_pos n value
  have := (bounds n).1
  omega

/-- The number of coefficients equal to one, counted on the polynomial's support. -/
def c (n : ℕ) : ℕ := ((product n).support.filter fun value => (product n).coeff value = 1).card

private theorem count_eq_total (n : ℕ) : c n = total n := by
  rw [c, product_support, card_eq_sum_ones, sum_filter]
  unfold total tally
  apply sum_bij (fun (value : ℕ) _ => (value : ℤ))
  · intro value member
    have := mem_range.mp member
    have := (bounds n).1
    simp only [mem_Ico]
    omega
  · intro first firstMem second secondMem equality
    exact_mod_cast equality
  · intro value member
    have limits := mem_Ico.mp member
    refine ⟨value.toNat, ?_, by omega⟩
    simp only [mem_range]
    omega
  · intro value member
    simp only [unique, multiplicity_eq_coeff]

/-- The empty product has one coefficient equal to one. -/
theorem c_zero : c 0 = 1 := by
  rw [count_eq_total]
  norm_num [total, tally, unique, span, multiplicity, Finset.sum_Ico_eq_sum_range]

/-- The first ternary factor has three coefficients equal to one. -/
theorem c_one : c 1 = 3 := by
  have initial : total 0 = 1 := (count_eq_total 0).symm.trans c_zero
  have emptyOverlap : overlap 0 = 0 := by norm_num [overlap, tally, span, G]
  have step := total_step 0
  rw [count_eq_total]
  simpa only [Nat.reduceAdd, initial, emptyOverlap, mul_zero, add_zero] using step

/-- The first two factors have nine coefficients equal to one. -/
theorem c_two : c 2 = 9 := by
  have initial : total 1 = 3 := (count_eq_total 1).symm.trans c_one
  have emptyOverlap : overlap 1 = 0 := by norm_num [overlap, tally, span, G]
  have step := total_step 1
  rw [count_eq_total]
  simpa only [Nat.reduceAdd, initial, emptyOverlap, mul_zero, add_zero] using step

/-- Stanley's all-index recurrence for coefficients equal to one. -/
theorem c_recurrence (n : ℕ) : c (n + 3) + c (n + 1) + c n = 3 * c (n + 2) := by
  simp only [count_eq_total]
  exact total_recurrence n

#print axioms G
#print axioms span
#print axioms multiplicity
#print axioms product
#print axioms span_overlap
#print axioms multiplicity_pos
#print axioms multiplicity_reflect
#print axioms multiplicity_eq_coeff
#print axioms product_support
#print axioms c
#print axioms c_zero
#print axioms c_one
#print axioms c_two
#print axioms c_recurrence

end

end D5.S1.Digit.StanleyTribleUniqueCoefficients
