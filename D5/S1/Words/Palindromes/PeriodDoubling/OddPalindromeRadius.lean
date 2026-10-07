/- GID: D5/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/OddPalindromeRadius
   mirror-E: none(waiver:exact-valuation-reflection-radius)
   anchors: []
   utility: none
   digest: Every integer center has an exact period-doubling reflection radius. -/

/-
proof_shape: content (odd_palindrome_radius)
escape_witness: Unequal valuations handle all off-scale reflections; exact obstructions occur at q or 3q.
admission_basis: escape-witness
Direct frozen dependencies: none; Word is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.Word

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- Positive-position center `2^r*u`, with the left boundary included in the radius. -/
theorem odd_palindrome_radius (r u R : ℕ) (hu : u % 2 = 1) (hR : R < 2 ^ r * u) :
    List.Palindrome (List.ofFn (fun i : Fin (2 * R + 1) =>
      u_pd (2 ^ r * u - R - 1 + i))) ↔
    R < if u = 1 then 2 ^ r else
      if max (padicValNat 2 (u - 1)) (padicValNat 2 (u + 1)) % 2 = 0 then
        2 ^ r else 3 * 2 ^ r := by
  have reflection_criterion :
    (∀ t : ℕ, t ≤ R →
      u_pd (2 ^ r * u - t - 1) = u_pd (2 ^ r * u + t - 1)) ↔
    R < if u = 1 then 2 ^ r else
      if max (padicValNat 2 (u - 1)) (padicValNat 2 (u + 1)) % 2 = 0 then
        2 ^ r else 3 * 2 ^ r := by
    let q := 2 ^ r
    have hq : 0 < q := by dsimp [q]; positivity
    have hu0 : 0 < u := by omega
    have hm : 0 < q * u := by positivity
    have word_val (x : ℕ) (hx : 0 < x) :
        u_pd (x - 1) = decide (padicValNat 2 x % 2 = 1) := by
      have hlt : x - 1 < 2 ^ x := by
        have hn := Nat.lt_two_pow_self (n := x)
        omega
      have h := (block_valuation x).2 (x - 1) hlt
      have he : x - 1 + 1 = x := by omega
      simpa [u_pd, he] using congrArg (fun z => z.getD false) h
    have scale_val (x : ℕ) (hx : 0 < x) :
        padicValNat 2 (q * x) = r + padicValNat 2 x := by
      rw [padicValNat.mul hq.ne' hx.ne']
      dsimp [q]
      rw [padicValNat.prime_pow]
    have hvm : padicValNat 2 (q * u) = r := by
      rw [scale_val u hu0, padicValNat.eq_zero_of_not_dvd (by omega : ¬2 ∣ u)]
      omega
    have unequal_val (m t : ℕ) (ht : 0 < t) (htm : t < m)
        (hval : padicValNat 2 t < padicValNat 2 m) :
        padicValNat 2 (m + t) = padicValNat 2 t ∧
          padicValNat 2 (m - t) = padicValNat 2 t := by
      have htq : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
      have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (lt_trans ht htm).ne'
      have hvq : padicValRat 2 (t : ℚ) < padicValRat 2 (m : ℚ) := by
        simp only [padicValRat.of_nat]
        exact_mod_cast hval
      constructor
      · have hz : (t : ℚ) + (m : ℚ) ≠ 0 := by positivity
        have h := padicValRat.add_eq_of_lt hz htq hmq hvq
        rw [add_comm, ← Nat.cast_add, padicValRat.of_nat, padicValRat.of_nat] at h
        exact_mod_cast h
      · have hz : -(t : ℚ) + (m : ℚ) ≠ 0 := by
          have hlt : (t : ℚ) < m := by exact_mod_cast htm
          linarith
        have hv : padicValRat 2 (-(t : ℚ)) < padicValRat 2 (m : ℚ) := by
          rw [padicValRat.neg]
          exact hvq
        have h := padicValRat.add_eq_of_lt hz (neg_ne_zero.mpr htq) hmq hv
        have he : -(t : ℚ) + (m : ℚ) = ((m - t : ℕ) : ℚ) := by
          rw [Nat.cast_sub htm.le]
          ring
        rw [he, padicValRat.neg, padicValRat.of_nat, padicValRat.of_nat] at h
        exact_mod_cast h
    have off_scale (t : ℕ) (ht : t < q * u) (hdiv : ¬q ∣ t) :
        u_pd (q * u - t - 1) = u_pd (q * u + t - 1) := by
      have ht0 : 0 < t := by
        by_contra hn
        have he : t = 0 := by omega
        exact hdiv (by simp [he])
      have hv : padicValNat 2 t < r := by
        by_contra hn
        apply hdiv
        exact (padicValNat_dvd_iff_le ht0.ne').mpr (by omega)
      have hv' : padicValNat 2 t < padicValNat 2 (q * u) := by omega
      obtain ⟨ha, hb⟩ := unequal_val (q * u) t ht0 ht hv'
      rw [word_val _ (by omega), word_val _ (by omega), ha, hb]
    have short (t : ℕ) (ht : t < q) :
        u_pd (q * u - t - 1) = u_pd (q * u + t - 1) := by
      by_cases ht0 : t = 0
      · simp [ht0]
      · have htm : t < q * u := by nlinarith
        apply off_scale t htm
        intro hd
        have hle := Nat.le_of_dvd (by omega : 0 < t) hd
        omega
    by_cases hu1 : u = 1
    · subst u
      change _ ↔ R < q
      constructor
      · intro _
        simpa [q] using hR
      · intro h
        intro t ht
        exact short t (by dsimp [q] at *; omega)
    · have hu2 : 2 < u := by omega
      have parity_eq (a b : ℕ) :
          (decide (a % 2 = 1) = decide (b % 2 = 1)) ↔ a % 2 = b % 2 := by
        by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1 <;> simp [ha, hb] <;> omega
      have val_two (x : ℕ) (hx : x % 4 = 2) : padicValNat 2 x = 1 := by
        have he : x = 2 * (x / 2) := by omega
        rw [he, padicValNat.mul (by decide : (2 : ℕ) ≠ 0) (by omega),
          padicValNat_self, padicValNat.eq_zero_of_not_dvd (by omega : ¬2 ∣ x / 2)]
      have val_four (x : ℕ) (hx : x % 8 = 4) : padicValNat 2 x = 2 := by
        have he : x = 4 * (x / 4) := by omega
        rw [he, padicValNat.mul (by decide : (4 : ℕ) ≠ 0) (by omega),
          padicValNat.eq_zero_of_not_dvd (by omega : ¬2 ∣ x / 4)]
        change padicValNat 2 (2 ^ 2) + 0 = 2
        rw [padicValNat.prime_pow]
      have adj :
          (2 ≤ padicValNat 2 (u - 1) ∧ padicValNat 2 (u + 1) = 1) ∨
          (padicValNat 2 (u - 1) = 1 ∧ 2 ≤ padicValNat 2 (u + 1)) := by
        by_cases hu4 : u % 4 = 1
        · left
          constructor
          · apply (padicValNat_dvd_iff_le (by omega : u - 1 ≠ 0)).mp
            norm_num
            omega
          · exact val_two _ (by omega)
        · right
          constructor
          · exact val_two _ (by omega)
          · apply (padicValNat_dvd_iff_le (by omega : u + 1 ≠ 0)).mp
            norm_num
            omega
      let s := max (padicValNat 2 (u - 1)) (padicValNat 2 (u + 1))
      have hs2 : 2 ≤ s := by dsimp [s]; rcases adj with h | h <;> omega
      have htq : q < q * u := by nlinarith
      have reflected_q :
          u_pd (q * u - q - 1) = u_pd (q * u + q - 1) ↔ s % 2 = 1 := by
        have hleft : q * u - q = q * (u - 1) := by
          rw [Nat.mul_sub_left_distrib, mul_one]
        have hright : q * u + q = q * (u + 1) := by ring
        rw [word_val _ (by omega), word_val _ (by omega),
          hleft, hright, scale_val _ (by omega), scale_val _ (by omega)]
        rw [parity_eq]
        dsimp [s]
        rcases adj with h | h
        · rw [h.2, max_eq_left (by omega)]
          omega
        · rw [h.1, max_eq_right (by omega)]
          omega
      change (∀ t : ℕ, t ≤ R → u_pd (q * u - t - 1) = u_pd (q * u + t - 1)) ↔
        R < if u = 1 then q else if s % 2 = 0 then q else 3 * q
      by_cases hseven : s % 2 = 0
      · simp only [if_neg hu1, if_pos hseven]
        constructor
        · intro h
          by_contra hn
          have hqR : q ≤ R := by dsimp [q] at *; omega
          have he := h q hqR
          have ho := reflected_q.mp he
          omega
        · intro h t ht
          exact short t (by dsimp [q] at *; omega)
      · have hsodd : s % 2 = 1 := by omega
        have hu8 : u % 8 = 1 ∨ u % 8 = 7 := by
          have hs3 : 3 ≤ s := by omega
          rcases adj with h | h
          · left
            have hv : 3 ≤ padicValNat 2 (u - 1) := by dsimp [s] at hs3; omega
            have hd := (padicValNat_dvd_iff_le (by omega : u - 1 ≠ 0)).mpr hv
            norm_num at hd
            omega
          · right
            have hv : 3 ≤ padicValNat 2 (u + 1) := by dsimp [s] at hs3; omega
            have hd := (padicValNat_dvd_iff_le (by omega : u + 1 ≠ 0)).mpr hv
            norm_num at hd
            omega
        have hu7 : 7 ≤ u := by rcases hu8 with h | h <;> omega
        have ht2 : 2 * q < q * u := by nlinarith
        have ht3 : 3 * q < q * u := by nlinarith
        have reflected_2q :
            u_pd (q * u - 2 * q - 1) = u_pd (q * u + 2 * q - 1) := by
          have hleft : q * u - 2 * q = q * (u - 2) := by
            rw [Nat.mul_sub_left_distrib]
            ring
          have hright : q * u + 2 * q = q * (u + 2) := by ring
          rw [word_val _ (by omega), word_val _ (by omega),
            hleft, hright, scale_val _ (by omega), scale_val _ (by omega),
            padicValNat.eq_zero_of_not_dvd (by omega : ¬2 ∣ u - 2),
            padicValNat.eq_zero_of_not_dvd (by omega : ¬2 ∣ u + 2)]
        have failure_3q :
            u_pd (q * u - 3 * q - 1) ≠ u_pd (q * u + 3 * q - 1) := by
          have hleft : q * u - 3 * q = q * (u - 3) := by
            rw [Nat.mul_sub_left_distrib]
            ring
          have hright : q * u + 3 * q = q * (u + 3) := by ring
          rw [word_val _ (by omega), word_val _ (by omega),
            hleft, hright, scale_val _ (by omega), scale_val _ (by omega)]
          rw [ne_eq, parity_eq]
          rcases hu8 with h | h
          · rw [val_two _ (by omega), val_four _ (by omega)]
            omega
          · rw [val_four _ (by omega), val_two _ (by omega)]
            omega
        simp only [if_neg hu1, if_neg hseven]
        constructor
        · intro h
          by_contra hn
          have ht : 3 * q ≤ R := by dsimp [q] at *; omega
          exact failure_3q (h _ ht)
        · intro h t ht
          have ht3 : t < 3 * q := by dsimp [q] at *; omega
          by_cases hd : q ∣ t
          · obtain ⟨k, hk⟩ := hd
            have hk3 : k < 3 := by nlinarith
            interval_cases k
            · simp [hk]
            · simpa [hk] using reflected_q.mpr hsodd
            · simpa [hk, mul_comm] using reflected_2q
          · exact off_scale t (by nlinarith) hd
  rw [← reflection_criterion]
  let m := 2 ^ r * u
  have hRm : R < m := hR
  change List.Palindrome (List.ofFn (fun i : Fin (2 * R + 1) =>
    u_pd (m - R - 1 + i))) ↔
      (∀ t : ℕ, t ≤ R → u_pd (m - t - 1) = u_pd (m + t - 1))
  let w := List.ofFn (fun i : Fin (2 * R + 1) => u_pd (m - R - 1 + i))
  constructor
  · intro hp t ht
    have hw : R - t < w.length := by simp [w]; omega
    have hwr : R - t < w.reverse.length := by simpa using hw
    have hrev : w.reverse = w := hp.reverse_eq
    have hv : w.reverse[R - t] = w[R - t] := by simp only [hrev]
    rw [List.getElem_reverse] at hv
    have he1 : m - R - 1 + (R - t) = m - t - 1 := by omega
    have he2 : m - R - 1 + (2 * R + 1 - 1 - (R - t)) = m + t - 1 := by omega
    simpa only [w, List.length_ofFn, List.getElem_ofFn, he1, he2] using hv.symm
  · intro h
    apply List.Palindrome.of_reverse_eq
    apply List.ext_getElem
    · simp
    · intro i hi hri
      rw [List.getElem_reverse]
      simp only [List.length_ofFn, List.getElem_ofFn]
      have hil : i < 2 * R + 1 := by simpa using hi
      by_cases him : i ≤ R
      · have ht : R - i ≤ R := by omega
        have he := h (R - i) ht
        have hleft : m - (R - i) - 1 = m - R - 1 + i := by omega
        have hright : m + (R - i) - 1 = m - R - 1 + (2 * R + 1 - 1 - i) := by omega
        simpa only [hleft, hright] using he.symm
      · have ht : i - R ≤ R := by omega
        have he := h (i - R) ht
        have hleft : m - (i - R) - 1 = m - R - 1 + (2 * R + 1 - 1 - i) := by omega
        have hright : m + (i - R) - 1 = m - R - 1 + i := by omega
        simpa only [hleft, hright] using he

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.odd_palindrome_radius
