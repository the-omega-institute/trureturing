/- GID: D5/S1/Digit/MurthyA085124
   generality: I
   mirror-B: D5/B/S1/Digit/MurthyA085124
   mirror-E: none(waiver:unbounded-decimal-classification)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: none
   digest: Positive decimal joint divisibility has an exact classification. -/

import D5.S1.Digit.DigitProductSlices
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.Prime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.GeomSum

/-! Decimal words connect Murthy's source predicate to ordinary base-ten digits.
The suffix construction follows N. S.; see Library/Digit/ns2016zerofreemultiples.md. -/

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
      convert Nat.mul_dvd_mul_left (p ^ k) hx using 1; ring

private def copies (w : List ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => w ++ copies w t

private theorem copies_good {w : List ℕ} (hw : Good w) (t : ℕ) : Good (copies w t) := by
  induction t with
  | zero => simp [copies, Good]
  | succ t ih => exact good_append hw ih

private theorem copies_value (w : List ℕ) (t : ℕ) :
    Nat.ofDigits 10 (copies w t) =
      Nat.ofDigits 10 w * ∑ i ∈ Finset.range t, (10 ^ w.length) ^ i := by
  induction t with
  | zero => simp [copies]
  | succ t ih =>
    rw [copies, Nat.ofDigits_append, ih]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, pow_succ]
    rw [← Finset.sum_mul]
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
    Nat.modEq_zero_iff_dvd.mp (by
      simpa using Nat.ModEq.sub (Nat.one_le_pow _ _ (by omega : 1 ≤ b))
        (by omega : 1 ≤ 1) he (Nat.ModEq.refl 1))
  rw [← geom_sum_mul_of_one_le (by omega : 1 ≤ b)] at hd
  exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < b - 1)).mp hd

private theorem decomposition (n : ℕ) (hn : 0 < n) (h10 : ¬ 10 ∣ n) :
    ∃ p k m : ℕ, (p = 2 ∨ p = 5) ∧ n = p ^ k * m ∧
      Nat.Coprime 10 m ∧ Nat.Coprime (p ^ k) m := by
  by_cases h2 : 2 ∣ n
  · obtain ⟨k, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 2 (by norm_num)
    have h5 : ¬ 5 ∣ m := by
      intro hd
      apply h10
      exact (by norm_num : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd h2
        (dvd_trans hd (he ▸ dvd_mul_left m (2 ^ k)))
    have hc2 : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.mpr hm
    have hc5 : Nat.Coprime 5 m := (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr h5
    exact ⟨2, k, m, Or.inl rfl, he, by simpa using hc2.mul_left hc5, hc2.pow_left k⟩
  · obtain ⟨k, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 5 (by norm_num)
    have h2m : ¬ 2 ∣ m := by
      intro hd
      apply h2
      exact dvd_trans hd (he ▸ dvd_mul_left m (5 ^ k))
    have hc2 : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.mpr h2m
    have hc5 : Nat.Coprime 5 m := (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hm
    exact ⟨5, k, m, Or.inr rfl, he, by simpa using hc2.mul_left hc5, hc5.pow_left k⟩

/-- The decimal predicate in the source includes positive N explicitly. -/
def admissible (n N : ℕ) : Prop :=
  0 < N ∧ n ∣ N ∧ 0 < digitProduct N ∧ n ∣ digitProduct N

/-- The source's least positive qualifying multiple, or zero if none exists. -/
noncomputable def a085124 (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ N, admissible n N then Nat.find h else 0

private theorem sufficiency (n : ℕ) (hn : 0 < n)
    (hs : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ≤ 7) (h10 : ¬ 10 ∣ n) :
    ∃ N, admissible n N := by
  obtain ⟨p, k, m, hp, he, hc10, hc⟩ := decomposition n hn h10
  obtain ⟨s, hsuf, hlen, hsd⟩ := suffix p hp k
  let w := s ++ (1 :: n.primeFactorsList)
  have hw : Good w := by
    apply good_append hsuf
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · norm_num
    · have hf := (Nat.mem_primeFactorsList hn.ne').mp hd
      exact ⟨hf.1.pos, lt_of_le_of_lt (hs d hf.1 hf.2) (by norm_num)⟩
  have hwne : w ≠ [] := by simp [w]
  have hp10 : p ∣ 10 := by rcases hp with rfl | rfl <;> norm_num
  have hwd : p ^ k ∣ Nat.ofDigits 10 w := by
    rw [Nat.ofDigits_append, hlen]
    exact dvd_add hsd (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hp10 k) _)
  have hwp : n ∣ w.prod := by
    dsimp [w]
    rw [List.prod_append, List.prod_cons, Nat.prod_primeFactorsList hn.ne', one_mul]
    exact dvd_mul_left n s.prod
  have hml : 0 < m := by
    have : m ≠ 0 := by intro h; simp [h] at he; omega
    omega
  have hbl : 1 < 10 ^ w.length := one_lt_pow₀ (by norm_num) (List.length_pos_iff.mpr hwne).ne'
  obtain ⟨t, ht, htd⟩ := repeat_multiple m (10 ^ w.length) hml hbl (hc10.pow_left _)
  let v := copies w t
  have hv := copies_good hw t
  have hvne : v ≠ [] := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    simp [v, copies, hwne]
  refine ⟨Nat.ofDigits 10 v, good_pos hv hvne, ?_, ?_, ?_⟩
  · rw [he, copies_value]
    apply hc.mul_dvd_of_dvd_of_dvd
    · exact dvd_mul_of_dvd_left hwd _
    · exact dvd_mul_of_dvd_right htd _
  · rw [digitProduct, good_digits hv]
    exact good_prod hv
  · rw [digitProduct, good_digits hv, copies_prod]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    rw [pow_succ]
    exact dvd_mul_of_dvd_right hwp _

private theorem necessity (n : ℕ) (h : ∃ N, admissible n N) :
    (∀ p : ℕ, Nat.Prime p → p ∣ n → p ≤ 7) ∧ ¬ 10 ∣ n := by
  obtain ⟨N, hN, hd, hp, hdp⟩ := h
  have hz : ∀ d ∈ Nat.digits 10 N, d ≠ 0 := by
    intro d hd h0
    subst d
    have := List.prod_eq_zero_iff.mpr hd
    change 0 < (Nat.digits 10 N).prod at hp
    omega
  constructor
  · intro p hprime hpn
    obtain ⟨d, hmem, hpd⟩ := (Nat.prime_iff.mp hprime).dvd_prod_iff.mp (dvd_trans hpn hdp)
    have hdpos : 0 < d := Nat.pos_of_ne_zero (hz d hmem)
    have hdlt : d < 10 := Nat.digits_lt_base (by norm_num) hmem
    have hple : p ≤ d := Nat.le_of_dvd hdpos hpd
    have : p < 10 := lt_of_le_of_lt hple hdlt
    by_contra hbound
    have hp89 : p = 8 ∨ p = 9 := by omega
    rcases hp89 with rfl | rfl <;> norm_num at hprime
  · intro h10
    have hN10 : 10 ∣ N := dvd_trans h10 hd
    have hmod : N % 10 = 0 := Nat.mod_eq_zero_of_dvd hN10
    have hdigits : Nat.digits 10 N = N % 10 :: Nat.digits 10 (N / 10) :=
      Nat.digits_def' (by norm_num) hN
    exact hz 0 (by rw [hdigits, hmod]; simp) rfl

/-- Murthy's classification, including the defining least-positive-or-zero bridge. -/
theorem result (n : ℕ) (hn : 0 < n) :
    ((∃ N, admissible n N) ↔
      (∀ p : ℕ, Nat.Prime p → p ∣ n → p ≤ 7) ∧ ¬ 10 ∣ n) ∧
    (0 < a085124 n ↔
      (∀ p : ℕ, Nat.Prime p → p ∣ n → p ≤ 7) ∧ ¬ 10 ∣ n) ∧
    (a085124 n = 0 ↔ ¬ ∃ N, admissible n N) ∧
    (0 < a085124 n → admissible n (a085124 n) ∧
      ∀ N, admissible n N → a085124 n ≤ N) := by
  classical
  have he : (∃ N, admissible n N) ↔
      (∀ p : ℕ, Nat.Prime p → p ∣ n → p ≤ 7) ∧ ¬ 10 ∣ n :=
    ⟨necessity n, fun h => sufficiency n hn h.1 h.2⟩
  refine ⟨he, ?_⟩
  by_cases hex : ∃ N, admissible n N
  · have ha : a085124 n = Nat.find hex := by simp [a085124, hex]
    have hs := Nat.find_spec hex
    have hp : 0 < a085124 n := by rw [ha]; exact hs.1
    refine ⟨⟨fun _ => he.mp hex, fun _ => hp⟩, ?_, ?_⟩
    · exact iff_of_false (by omega) (not_not.mpr hex)
    · intro _
      rw [ha]
      exact ⟨hs, fun N hN => Nat.find_min' hex hN⟩
  · have ha : a085124 n = 0 := by simp [a085124, hex]
    refine ⟨?_, by simp [ha, hex], ?_⟩
    · rw [ha]
      exact ⟨by omega, fun h => (hex (he.mpr h)).elim⟩
    · simp [ha]

#print axioms result

end D5.S1.Digit.MurthyA085124
