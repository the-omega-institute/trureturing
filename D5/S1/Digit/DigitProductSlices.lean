/- GID: D5/S1/Digit/DigitProductSlices
   generality: I
   mirror-B: D5/B/S1/Digit/DigitProductSlices
   mirror-E: none(waiver:exact-finite-decimal-classification)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   digest: The zero-3 and one-3 digit-product slices over digits 2, 3, and 6 are classified. -/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository name and conclusion-shape searches found no decimal
     digit-product classification in D5, and neither target atom occurs in an
     in-flight lane.
   * Pinned Mathlib supplies decimal digit reconstruction, suffix reduction,
     list counting, and arithmetic tactics, but no theorem classifying either
     the zero-3 or one-3 slice.
   * The unique-3 proof removes that digit to obtain the live 2-adic product
     bound, rules out all 81 permitted four-digit suffixes modulo 16, and then
     exhausts the lists of length at most four. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.DigitProductSlices

/-- Product of the base-ten digits of `N`, read least significant first. -/
def digitProduct (N : ℕ) : ℕ := (Nat.digits 10 N).prod

/-- Every base-ten digit of `N` is one of 2, 3, or 6. -/
def AllDigitsIn236 (N : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 N, d ∈ ({2, 3, 6} : Finset ℕ)

/-- Number of occurrences of the digit 3 in the base-ten expansion of `N`. -/
def countThree (N : ℕ) : ℕ := (Nat.digits 10 N).count 3

private theorem four_dvd_prod_of_two_even (l : List ℕ)
    (hlen : 2 ≤ l.length) (heven : ∀ d ∈ l, 2 ∣ d) : 4 ∣ l.prod := by
  rcases l with _ | ⟨a, l⟩
  · simp at hlen
  rcases l with _ | ⟨b, l⟩
  · simp at hlen
  have ha : 2 ∣ a := heven a (by simp)
  have hb : 2 ∣ b := heven b (by simp)
  rcases ha with ⟨a, rfl⟩
  rcases hb with ⟨b, rfl⟩
  refine ⟨a * b * l.prod, ?_⟩
  simp only [List.prod_cons]
  ring

private theorem two_pow_length_dvd_prod_of_all_even (l : List ℕ)
    (heven : ∀ d ∈ l, 2 ∣ d) : 2 ^ l.length ∣ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : 2 ∣ a := heven a (by simp)
      have hl : ∀ d ∈ l, 2 ∣ d := by
        intro d hd
        exact heven d (by simp [hd])
      rcases ha with ⟨a, rfl⟩
      rcases ih hl with ⟨k, hk⟩
      refine ⟨a * k, ?_⟩
      simp only [List.length_cons, List.prod_cons, pow_succ]
      rw [hk]
      ring

private theorem one_three_two_adic_lower_bound (l : List ℕ)
    (hall : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ))
    (hcount : l.count 3 = 1) : 2 ^ (l.length - 1) ∣ l.prod := by
  have hmem : 3 ∈ l := List.count_pos_iff.mp (by omega)
  obtain ⟨a, b, rfl⟩ := List.mem_iff_append.mp hmem
  simp only [List.count_append, List.count_cons, beq_self_eq_true, ↓reduceIte] at hcount
  have hca : a.count 3 = 0 := by omega
  have hcb : b.count 3 = 0 := by omega
  have heven : ∀ d ∈ a ++ b, 2 ∣ d := by
    intro d hd
    have hdab : d ∈ a ∨ d ∈ b := List.mem_append.mp hd
    have hdall : d ∈ a ++ 3 :: b := by
      rcases hdab with ha | hb
      · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ (by simp [hb])
    have hd236 := hall d hdall
    have hdne : d ≠ 3 := by
      intro h
      subst d
      rcases hdab with ha | hb
      · exact (List.count_eq_zero.mp hca) ha
      · exact (List.count_eq_zero.mp hcb) hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd236
    rcases hd236 with rfl | rfl | rfl
    · norm_num
    · exact (hdne rfl).elim
    · norm_num
  rcases two_pow_length_dvd_prod_of_all_even (a ++ b) heven with ⟨k, hk⟩
  refine ⟨3 * k, ?_⟩
  simp only [List.length_append, List.length_cons, List.prod_append, List.prod_cons] at hk ⊢
  calc
    a.prod * (3 * b.prod) = 3 * (a.prod * b.prod) := by ring
    _ = 3 * (2 ^ (a.length + b.length) * k) := by rw [hk]
    _ = 2 ^ (a.length + b.length) * (3 * k) := by ring

private theorem one_three_product_divisible_by_sixteen (l : List ℕ)
    (hall : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ))
    (hcount : l.count 3 = 1) (hlen : 5 ≤ l.length) : 16 ∣ l.prod := by
  have hbound := one_three_two_adic_lower_bound l hall hcount
  have hexp : 4 ≤ l.length - 1 := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hexp
  have h16pow : 16 ∣ 2 ^ (l.length - 1) := by
    rw [hk, pow_add]
    norm_num
  exact dvd_trans h16pow hbound

private theorem no_permitted_four_digit_suffix_divisible_by_sixteen (l : List ℕ)
    (hlen : l.length = 4)
    (hall : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ))
    (hcount : l.count 3 ≤ 1) :
    ¬ 16 ∣ Nat.ofDigits 10 l := by
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hlen
  have ha := hall a (by simp)
  have hb := hall b (by simp)
  have hc := hall c (by simp)
  have hd := hall d (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  rcases ha with (rfl | rfl | rfl) <;>
    rcases hb with (rfl | rfl | rfl) <;>
      rcases hc with (rfl | rfl | rfl) <;>
        rcases hd with (rfl | rfl | rfl)
  all_goals try norm_num at hcount
  all_goals norm_num [Nat.ofDigits]

private theorem no_zero_three_two_digit_suffix_divisible_by_four (l : List ℕ)
    (hlen : l.length = 2)
    (hall : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ))
    (hcount : l.count 3 = 0) : ¬ 4 ∣ Nat.ofDigits 10 l := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := hall a (by simp)
  have hb := hall b (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with (rfl | rfl | rfl) <;>
    rcases hb with (rfl | rfl | rfl)
  all_goals try norm_num at hcount
  all_goals norm_num [Nat.ofDigits]

private theorem short_one_three_classification (l : List ℕ)
    (hlen : l.length ≤ 4)
    (hall : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ))
    (hcount : l.count 3 = 1) :
    (l.prod ∣ Nat.ofDigits 10 l ↔
      Nat.ofDigits 10 l = 3 ∨ Nat.ofDigits 10 l = 36 ∨ Nat.ofDigits 10 l = 2232) := by
  rcases l with _ | ⟨a, l⟩
  · simp at hcount
  rcases l with _ | ⟨b, l⟩
  · have ha := hall a (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with (rfl | rfl | rfl)
    all_goals try norm_num at hcount
    all_goals norm_num [Nat.ofDigits]
  rcases l with _ | ⟨c, l⟩
  · have ha := hall a (by simp)
    have hb := hall b (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with (rfl | rfl | rfl) <;>
      rcases hb with (rfl | rfl | rfl)
    all_goals try norm_num at hcount
    all_goals norm_num [Nat.ofDigits]
  rcases l with _ | ⟨d, l⟩
  · have ha := hall a (by simp)
    have hb := hall b (by simp)
    have hc := hall c (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with (rfl | rfl | rfl) <;>
      rcases hb with (rfl | rfl | rfl) <;>
        rcases hc with (rfl | rfl | rfl)
    all_goals try norm_num at hcount
    all_goals norm_num [Nat.ofDigits]
  rcases l with _ | ⟨e, l⟩
  · have ha := hall a (by simp)
    have hb := hall b (by simp)
    have hc := hall c (by simp)
    have hd := hall d (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
    rcases ha with (rfl | rfl | rfl) <;>
      rcases hb with (rfl | rfl | rfl) <;>
        rcases hc with (rfl | rfl | rfl) <;>
          rcases hd with (rfl | rfl | rfl)
    all_goals try norm_num at hcount
    all_goals norm_num [Nat.ofDigits]
  simp at hlen
  omega

private theorem short_zero_three_classification (l : List ℕ)
    (hlen : l.length ≤ 1)
    (hall : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ))
    (hcount : l.count 3 = 0) (hpos : 0 < Nat.ofDigits 10 l) :
    (l.prod ∣ Nat.ofDigits 10 l ↔ Nat.ofDigits 10 l = 2 ∨ Nat.ofDigits 10 l = 6) := by
  rcases l with _ | ⟨a, l⟩
  · norm_num [Nat.ofDigits] at hpos
  rcases l with _ | ⟨b, l⟩
  · have ha := hall a (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with (rfl | rfl | rfl)
    all_goals try norm_num at hcount
    all_goals norm_num [Nat.ofDigits]
  simp at hlen

/-- Positive numbers over digits 2, 3, and 6 with no digit 3 are exactly 2
and 6 among the numbers divisible by their digit product. -/
theorem zero_three_slice (N : ℕ) (hpos : 0 < N)
    (hall : AllDigitsIn236 N) (hcount : countThree N = 0) :
    (digitProduct N ∣ N ↔ N = 2 ∨ N = 6) := by
  let l := Nat.digits 10 N
  have hall' : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ) := hall
  have hcount' : l.count 3 = 0 := hcount
  have hN : Nat.ofDigits 10 l = N := Nat.ofDigits_digits 10 N
  constructor
  · intro hdvd
    by_contra hshort
    have hlen : 2 ≤ l.length := by
      by_contra h
      have hle : l.length ≤ 1 := by omega
      have hpos' : 0 < Nat.ofDigits 10 l := by simpa [hN] using hpos
      have hs := (short_zero_three_classification l hle hall' hcount' hpos').mp
      have hdvd' : l.prod ∣ Nat.ofDigits 10 l := by
        rw [hN]
        simpa [digitProduct, l] using hdvd
      exact hshort (by simpa [hN] using hs hdvd')
    have heven : ∀ d ∈ l, 2 ∣ d := by
      intro d hd
      have hd236 := hall' d hd
      have hdne : d ≠ 3 := by
        intro h
        subst d
        exact (List.count_eq_zero.mp hcount') hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd236
      rcases hd236 with rfl | rfl | rfl
      · norm_num
      · exact (hdne rfl).elim
      · norm_num
    have h4prod : 4 ∣ l.prod := four_dvd_prod_of_two_even l hlen heven
    have h4N : 4 ∣ N := dvd_trans h4prod (by simpa [digitProduct, l] using hdvd)
    have h4pow : 4 ∣ 10 ^ 2 := by norm_num
    have h4mod : 4 ∣ N % 10 ^ 2 := (Nat.dvd_mod_iff h4pow).2 h4N
    rw [Nat.self_mod_pow_eq_ofDigits_take 2 N (by norm_num)] at h4mod
    have htakeLen : (l.take 2).length = 2 := by
      rw [List.length_take]
      omega
    have htakeAll : ∀ d ∈ l.take 2, d ∈ ({2, 3, 6} : Finset ℕ) := by
      intro d hd
      exact hall' d (List.mem_of_mem_take hd)
    have htakeCount : (l.take 2).count 3 = 0 :=
      List.count_eq_zero.mpr fun hmem => (List.count_eq_zero.mp hcount')
        (List.mem_of_mem_take hmem)
    exact (no_zero_three_two_digit_suffix_divisible_by_four
      (l.take 2) htakeLen htakeAll htakeCount) h4mod
  · intro h
    rcases h with rfl | rfl <;> decide

/-- Numbers over digits 2, 3, and 6 with exactly one digit 3 are exactly 3,
36, and 2232 among the numbers divisible by their digit product. -/
theorem one_three_slice (N : ℕ) (hall : AllDigitsIn236 N)
    (hcount : countThree N = 1) :
    (digitProduct N ∣ N ↔ N = 3 ∨ N = 36 ∨ N = 2232) := by
  let l := Nat.digits 10 N
  have hall' : ∀ d ∈ l, d ∈ ({2, 3, 6} : Finset ℕ) := hall
  have hcount' : l.count 3 = 1 := hcount
  have hN : Nat.ofDigits 10 l = N := Nat.ofDigits_digits 10 N
  constructor
  · intro hdvd
    by_contra hshort
    have hlen : 5 ≤ l.length := by
      by_contra h
      have hle : l.length ≤ 4 := by omega
      have hs := (short_one_three_classification l hle hall' hcount').mp
      have hdvd' : l.prod ∣ Nat.ofDigits 10 l := by
        rw [hN]
        simpa [digitProduct, l] using hdvd
      exact hshort (by simpa [hN] using hs hdvd')
    have h16prod : 16 ∣ l.prod :=
      one_three_product_divisible_by_sixteen l hall' hcount' hlen
    have h16N : 16 ∣ N := dvd_trans h16prod (by simpa [digitProduct, l] using hdvd)
    have h16pow : 16 ∣ 10 ^ 4 := by norm_num
    have h16mod : 16 ∣ N % 10 ^ 4 := (Nat.dvd_mod_iff h16pow).2 h16N
    rw [Nat.self_mod_pow_eq_ofDigits_take 4 N (by norm_num)] at h16mod
    have htakeLen : (l.take 4).length = 4 := by
      rw [List.length_take]
      omega
    have htakeAll : ∀ d ∈ l.take 4, d ∈ ({2, 3, 6} : Finset ℕ) := by
      intro d hd
      exact hall' d (List.mem_of_mem_take hd)
    have htakeCount : (l.take 4).count 3 ≤ 1 := by
      calc
        (l.take 4).count 3 ≤ (l.take 4).count 3 + (l.drop 4).count 3 :=
          Nat.le_add_right _ _
        _ = l.count 3 := by rw [← List.count_append, List.take_append_drop]
        _ = 1 := hcount'
    exact (no_permitted_four_digit_suffix_divisible_by_sixteen
      (l.take 4) htakeLen htakeAll htakeCount) h16mod
  · intro h
    rcases h with rfl | rfl | rfl <;> decide

-- Fidelity witnesses: both theorem domains are inhabited and their hypotheses
-- are jointly satisfiable in the pinned toolchain.
example : 0 < (6 : ℕ) ∧ AllDigitsIn236 6 ∧ countThree 6 = 0 := by
  constructor
  · norm_num
  constructor
  · simp [AllDigitsIn236]
  · decide
example : AllDigitsIn236 2232 ∧ countThree 2232 = 1 := by
  constructor
  · simp [AllDigitsIn236]
  · decide

-- The predicates have nontrivial negative instances; the classifications are
-- not definitionally true or restatements of their hypotheses.
example : ¬ digitProduct 236 ∣ 236 := by decide
example : ¬ digitProduct 22232 ∣ 22232 := by decide

#print axioms zero_three_slice
#print axioms one_three_slice

end D5.S1.Digit.DigitProductSlices
