/- GID: D5/S1/Digit/MurthyA085124
   generality: I
   mirror-B: D5/B/S1/Digit/MurthyA085124
   mirror-E: none(waiver:unbounded-decimal-classification)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: none
   digest: Joint divisibility of a positive decimal integer and its positive digit product is classified. -/

import D5.S1.Digit.DigitProductSlices
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.Prime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.MurthyA085124

open scoped BigOperators
open D5.S1.Digit.DigitProductSlices (digitProduct)

private def Good (w : List ℕ) : Prop := ∀ d ∈ w, 0 < d ∧ d < 10

private theorem good_append {a b : List ℕ} (ha : Good a) (hb : Good b) : Good (a ++ b) := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact ha d hd
  · exact hb d hd

private theorem good_digits {w : List ℕ} (hw : Good w) :
    Nat.digits 10 (Nat.ofDigits 10 w) = w := by
  apply Nat.digits_ofDigits 10 (by norm_num) w (fun d hd => (hw d hd).2)
  intro hn
  exact (hw _ (List.getLast_mem hn)).1.ne'

private theorem good_pos {w : List ℕ} (hw : Good w) (hne : w ≠ []) :
    0 < Nat.ofDigits 10 w := by
  rcases w with _ | ⟨d, w⟩
  · exact (hne rfl).elim
  have hd := (hw d (by simp)).1
  rw [Nat.ofDigits_cons]
  omega

private theorem good_prod {w : List ℕ} (hw : Good w) : 0 < w.prod := by
  exact List.prod_pos (fun d hd => (hw d hd).1)

private theorem choose_digit (p c u : ℕ) (hp : 1 < p) (hc : c.Coprime p) :
    ∃ x, 0 < x ∧ x ≤ p ∧ p ∣ u + c * x := by
  obtain ⟨m, hm, he⟩ := Nat.exists_mul_mod_eq_of_coprime (p - (u + c) % p) hc (by omega)
  refine ⟨m + 1, by omega, by omega, Nat.dvd_of_mod_eq_zero ?_⟩
  have hr : (u + c) % p ≤ p := (Nat.mod_lt _ (by omega)).le
  calc
    (u + c * (m + 1)) % p = ((u + c) % p + (c * m) % p) % p := by
      rw [← Nat.add_mod]; congr 1; ring
    _ = ((u + c) % p + (p - (u + c) % p) % p) % p := by rw [he]
    _ = 0 := by rw [Nat.add_mod_mod, Nat.add_sub_of_le hr, Nat.mod_self]

/-- The digit-lifting construction is the zero-free suffix mechanism of N. S. -/
private theorem suffix (p : ℕ) (hp : p = 2 ∨ p = 5) (k : ℕ) :
    ∃ w : List ℕ, Good w ∧ w.length = k ∧ p ^ k ∣ Nat.ofDigits 10 w := by
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  have hp1 : 1 < p := by rcases hp with rfl | rfl <;> norm_num
  have hfac : p * (10 / p) = 10 := by rcases hp with rfl | rfl <;> norm_num
  have hcop : (10 / p).Coprime p := by rcases hp with rfl | rfl <;> norm_num
  induction k with
  | zero => exact ⟨[], by simp [Good], rfl, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, hl, u, hu⟩ := ih
    obtain ⟨x, hx0, hxp, hx⟩ := choose_digit p ((10 / p) ^ k) u hp1 (hcop.pow_left k)
    refine ⟨w ++ [x], good_append hw ?_, by simp [hl], ?_⟩
    · intro d hd
      have : d = x := by simpa using hd
      subst d
      exact ⟨hx0, lt_of_le_of_lt hxp (by rcases hp with rfl | rfl <;> norm_num)⟩
    · rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hl, hu]
      have ht : 10 ^ k = p ^ k * (10 / p) ^ k := by rw [← mul_pow, hfac]
      rw [ht, pow_succ]
      convert dvd_mul_of_dvd_right hx (p ^ k) using 1 <;> ring

private def copies (w : List ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => w ++ copies w t

private theorem copies_good {w : List ℕ} (hw : Good w) (t : ℕ) : Good (copies w t) := by
  induction t with
  | zero => simp [copies, Good]
  | succ t ih => exact good_append hw ih

private theorem copies_value (w : List ℕ) (t : ℕ) :
    Nat.ofDigits 10 (copies w t) = Nat.ofDigits 10 w * ∑ i ∈ Finset.range t, (10 ^ w.length) ^ i := by
  induction t with
  | zero => simp [copies]
  | succ t ih =>
    rw [copies, Nat.ofDigits_append, ih]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one, pow_succ]
    rw [← Finset.mul_sum]
    ring

private theorem copies_prod (w : List ℕ) (t : ℕ) : (copies w t).prod = w.prod ^ t := by
  induction t with
  | zero => simp [copies]
  | succ t ih => simp [copies, ih, pow_succ, mul_comm]

private theorem repeat_multiple (m b : ℕ) (hm : 0 < m) (hb : 1 < b) (hc : b.Coprime m) :
    ∃ t, 0 < t ∧ m ∣ ∑ i ∈ Finset.range t, b ^ i := by
  let q := m * (b - 1)
  have hq : 0 < q := Nat.mul_pos hm (by omega)
  have hcop : b.Coprime q := hc.mul_right ((Nat.coprime_self_sub_right (by omega)).2 (by simp))
  refine ⟨Nat.totient q, Nat.totient_pos.mpr hq, ?_⟩
  have he := Nat.ModEq.pow_totient hcop
  have hd : q ∣ b ^ Nat.totient q - 1 :=
    Nat.modEq_zero_iff_dvd.mp (by simpa using he.sub (Nat.ModEq.refl 1))
  rw [← geom_sum_mul_of_one_le (by omega : 1 ≤ b)] at hd
  exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < b - 1)).mp hd

end D5.S1.Digit.MurthyA085124
