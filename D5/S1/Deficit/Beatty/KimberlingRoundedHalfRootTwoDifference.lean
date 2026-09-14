/- GID: D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Real.Irrational]
   utility: none
   digest: Round(n/sqrt 2) changes by zero or one at complementary shifted Beatty positions. -/

import Mathlib.NumberTheory.Real.Irrational

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Beatty.KimberlingRoundedHalfRootTwoDifference

/-- OEIS A049473: the nearest integer to `n / sqrt 2`. -/
noncomputable def a (n : ℕ) : ℤ :=
  round ((n : ℝ) / Real.sqrt 2)

/-- OEIS A001953, the lower shifted Beatty sequence in the conjecture. -/
noncomputable def lower (k : ℕ) : ℤ :=
  ⌊((k : ℝ) + 1 / 2) * Real.sqrt 2⌋

/-- OEIS A001954, the upper shifted Beatty sequence in the conjecture. -/
noncomputable def upper (k : ℕ) : ℤ :=
  ⌊((k : ℝ) + 1 / 2) * (2 + Real.sqrt 2)⌋

/-- The difference clause of Clark Kimberling's 2014 OEIS conjecture on A049473. -/
theorem result : ∀ n : ℕ,
    (a (n + 1) - a n = 0 ∨ a (n + 1) - a n = 1) ∧
    (a (n + 1) - a n = 1 ↔ ∃ k : ℕ, (n : ℤ) = lower k) ∧
    (a (n + 1) - a n = 0 ↔ ∃ k : ℕ, (n : ℤ) = upper k) := by
  intro n
  let r : ℝ := Real.sqrt 2
  let x : ℕ → ℝ := fun m ↦ (m : ℝ) / r + 1 / 2
  let ell : ℕ → ℝ := fun k ↦ ((k : ℝ) + 1 / 2) * r
  let ups : ℕ → ℝ := fun k ↦ ((k : ℝ) + 1 / 2) * (2 + r)
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hrsq : r * r = 2 := by
    dsimp [r]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hrone : 1 < r := by nlinarith
  have hqpos : 0 < 1 / r := one_div_pos.2 hrpos
  have hqlt : 1 / r < 1 := by
    rw [div_lt_iff₀ hrpos]
    simpa using hrone
  have hspos : 0 < 2 + r := by positivity
  have hconj : 1 / (2 + r) = 1 - 1 / r := by
    field_simp [ne_of_gt hrpos, ne_of_gt hspos]
    nlinarith
  have hconj_inv : (2 + r)⁻¹ = 1 - 1 / r := by simpa [one_div] using hconj
  have hdiv_conj (t : ℝ) : t / (2 + r) = t * (1 - 1 / r) := by
    rw [div_eq_mul_inv, hconj_inv]
  have ha_floor (m : ℕ) : a m = ⌊x m⌋ := by
    simp [a, x, r, round_eq]
  have hstep (m : ℕ) : x (m + 1) = x m + 1 / r := by
    simp only [x, Nat.cast_add, Nat.cast_one]
    ring
  have hlower (k : ℕ) : lower k = ⌊ell k⌋ := by
    simp [lower, ell, r]
  have hupper (k : ℕ) : upper k = ⌊ups k⌋ := by
    simp [upper, ups, r]
  have hell_irr (k : ℕ) : Irrational (ell k) := by
    rw [show ell k = ((2 * k + 1 : ℕ) : ℝ) * Real.sqrt 2 / 2 by
      simp only [ell, r, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring]
    exact (irrational_sqrt_two.natCast_mul (show 2 * k + 1 ≠ 0 by omega)).div_natCast
      (show (2 : ℕ) ≠ 0 by norm_num)
  have hvalues : a (n + 1) - a n = 0 ∨ a (n + 1) - a n = 1 := by
    rw [ha_floor (n + 1), ha_floor n]
    have hmono : ⌊x n⌋ ≤ ⌊x (n + 1)⌋ := by
      apply Int.floor_mono
      rw [hstep]
      linarith
    have hupp : ⌊x (n + 1)⌋ ≤ ⌊x n⌋ + 1 := by
      rw [← Int.floor_add_one]
      apply Int.floor_mono
      rw [hstep]
      linarith
    omega
  have hjump : a (n + 1) - a n = 1 ↔ ∃ k : ℕ, (n : ℤ) = lower k := by
    constructor
    · intro hd
      rw [ha_floor (n + 1), ha_floor n] at hd
      have heq : ⌊x (n + 1)⌋ = ⌊x n⌋ + 1 := by omega
      let m : ℤ := ⌊x n⌋
      have hm0 : 0 ≤ m := by
        apply Int.floor_nonneg.2
        dsimp [x]
        positivity
      let k : ℕ := m.toNat
      have hkz : (k : ℤ) = m := by
        simpa [k] using Int.toNat_of_nonneg hm0
      have hkr : (k : ℝ) = (m : ℝ) := by exact_mod_cast hkz
      refine ⟨k, ?_⟩
      rw [hlower]
      symm
      apply Int.floor_eq_iff.2
      have hxlt : x n < (m : ℝ) + 1 := by
        change x n < (↑⌊x n⌋ : ℝ) + 1
        exact Int.lt_floor_add_one (x n)
      have hxnextle : (m : ℝ) + 1 ≤ x (n + 1) := by
        have h := Int.floor_le (x (n + 1))
        rw [heq] at h
        simpa [m] using h
      have hdivlt : (n : ℝ) / r < (m : ℝ) + 1 / 2 := by
        dsimp [x] at hxlt
        linarith
      have hnltm : (n : ℝ) < ((m : ℝ) + 1 / 2) * r :=
        (div_lt_iff₀ hrpos).1 hdivlt
      have hdivle : (m : ℝ) + 1 / 2 ≤ ((n + 1 : ℕ) : ℝ) / r := by
        dsimp [x] at hxnextle
        linarith
      have hmle : ((m : ℝ) + 1 / 2) * r ≤ ((n + 1 : ℕ) : ℝ) :=
        (le_div_iff₀ hrpos).1 hdivle
      have hnlt : (n : ℝ) < ell k := by
        dsimp [ell]
        rw [hkr]
        exact hnltm
      have hle : ell k ≤ ((n + 1 : ℕ) : ℝ) := by
        dsimp [ell]
        rw [hkr]
        exact hmle
      have hlt : ell k < ((n + 1 : ℕ) : ℝ) :=
        lt_of_le_of_ne hle ((hell_irr k).ne_nat (n + 1))
      constructor
      · exact hnlt.le
      · change ell k < (n : ℝ) + 1
        simpa only [Nat.cast_add, Nat.cast_one] using hlt
    · rintro ⟨k, hk⟩
      have hkfloor : ⌊ell k⌋ = (n : ℤ) := by simpa [hlower k] using hk.symm
      have hb := Int.floor_eq_iff.1 hkfloor
      have hnlt : (n : ℝ) < ell k :=
        lt_of_le_of_ne hb.1 ((hell_irr k).ne_nat n).symm
      have hdivn : (n : ℝ) / r < (k : ℝ) + 1 / 2 := by
        apply (div_lt_iff₀ hrpos).2
        simpa [ell] using hnlt
      have hdivnext : (k : ℝ) + 1 / 2 < ((n + 1 : ℕ) : ℝ) / r := by
        apply (lt_div_iff₀ hrpos).2
        simpa [ell, Nat.cast_add, Nat.cast_one] using hb.2
      have hxnupper : x n < (k : ℝ) + 1 := by
        dsimp [x]
        linarith
      have hxnextlower : (k : ℝ) + 1 < x (n + 1) := by
        dsimp [x]
        linarith
      have hxnlower : (k : ℝ) ≤ x n := by
        rw [hstep] at hxnextlower
        linarith
      have hxnextupper : x (n + 1) < (k : ℝ) + 2 := by
        rw [hstep]
        linarith
      have hfloor_n : ⌊x n⌋ = (k : ℤ) := Int.floor_eq_iff.2 ⟨hxnlower, hxnupper⟩
      have hfloor_next : ⌊x (n + 1)⌋ = (k : ℤ) + 1 := by
        apply Int.floor_eq_iff.2
        constructor
        · exact_mod_cast hxnextlower.le
        · norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_one]
          linarith
      rw [ha_floor (n + 1), ha_floor n, hfloor_next, hfloor_n]
      omega
  have hzero : a (n + 1) - a n = 0 ↔ ∃ k : ℕ, (n : ℤ) = upper k := by
    constructor
    · intro hd
      rw [ha_floor (n + 1), ha_floor n] at hd
      have heq : ⌊x (n + 1)⌋ = ⌊x n⌋ := by omega
      let m : ℤ := ⌊x n⌋
      have hmle : m ≤ (n : ℤ) := by
        have hdiv : (n : ℝ) / r ≤ (n : ℝ) := by
          rw [div_le_iff₀ hrpos]
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.2 hrone.le)]
        have hxlt : x n < (n : ℝ) + 1 := by
          dsimp [x]
          linarith
        have hfloorlt : m < (n : ℤ) + 1 := by
          apply Int.floor_lt.2
          simpa [m, Int.cast_add, Int.cast_natCast, Int.cast_one] using hxlt
        omega
      let z : ℤ := (n : ℤ) - m
      have hz0 : 0 ≤ z := by simp [z, hmle]
      let k : ℕ := z.toNat
      have hkz : (k : ℤ) = z := by simpa [k] using Int.toNat_of_nonneg hz0
      have hkr : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkz
      refine ⟨k, ?_⟩
      rw [hupper]
      symm
      apply Int.floor_eq_iff.2
      have hm_lower : (m : ℝ) ≤ x n := by
        simpa [m] using Int.floor_le (x n)
      have hm_upper : x (n + 1) < (m : ℝ) + 1 := by
        have h := Int.lt_floor_add_one (x (n + 1))
        rw [heq] at h
        simpa [m] using h
      have hleftdiv : (n : ℝ) / (2 + r) ≤ (z : ℝ) + 1 / 2 := by
        rw [hdiv_conj]
        dsimp [x, z] at hm_lower ⊢
        push_cast
        ring_nf at hm_lower ⊢
        linarith
      have hrightdiv : (z : ℝ) + 1 / 2 < ((n + 1 : ℕ) : ℝ) / (2 + r) := by
        rw [hdiv_conj]
        dsimp [x, z] at hm_upper ⊢
        push_cast
        ring_nf at hm_upper ⊢
        norm_num only [Nat.cast_add, Nat.cast_one] at hm_upper
        ring_nf at hm_upper
        linarith
      have hleft : (n : ℝ) ≤ ((z : ℝ) + 1 / 2) * (2 + r) :=
        (div_le_iff₀ hspos).1 hleftdiv
      have hright : ((z : ℝ) + 1 / 2) * (2 + r) < ((n + 1 : ℕ) : ℝ) :=
        (lt_div_iff₀ hspos).1 hrightdiv
      constructor
      · dsimp [ups]
        rw [hkr]
        exact hleft
      · dsimp [ups]
        rw [hkr]
        change ((z : ℝ) + 1 / 2) * (2 + r) < (n : ℝ) + 1
        simpa only [Nat.cast_add, Nat.cast_one] using hright
    · rintro ⟨k, hk⟩
      have hkfloor : ⌊ups k⌋ = (n : ℤ) := by simpa [hupper k] using hk.symm
      have hb := Int.floor_eq_iff.1 hkfloor
      have hleftdiv : (n : ℝ) / (2 + r) ≤ (k : ℝ) + 1 / 2 := by
        apply (div_le_iff₀ hspos).2
        simpa [ups] using hb.1
      have hrightdiv : (k : ℝ) + 1 / 2 < ((n + 1 : ℕ) : ℝ) / (2 + r) := by
        apply (lt_div_iff₀ hspos).2
        simpa [ups, Nat.cast_add, Nat.cast_one] using hb.2
      let z : ℤ := (n : ℤ) - (k : ℤ)
      have hzlower : (z : ℝ) ≤ x n := by
        rw [hdiv_conj] at hleftdiv
        dsimp [z, x] at hleftdiv ⊢
        push_cast at hleftdiv ⊢
        ring_nf at hleftdiv ⊢
        linarith
      have hzupper : x (n + 1) < (z : ℝ) + 1 := by
        rw [hdiv_conj] at hrightdiv
        dsimp [z, x] at hrightdiv ⊢
        push_cast at hrightdiv ⊢
        ring_nf at hrightdiv ⊢
        linarith
      have hxmono : x n ≤ x (n + 1) := by
        rw [hstep]
        linarith
      have hfloor_n : ⌊x n⌋ = z := Int.floor_eq_iff.2 ⟨hzlower, hxmono.trans_lt hzupper⟩
      have hfloor_next : ⌊x (n + 1)⌋ = z :=
        Int.floor_eq_iff.2 ⟨hzlower.trans hxmono, hzupper⟩
      rw [ha_floor (n + 1), ha_floor n, hfloor_next, hfloor_n]
      omega
  exact ⟨hvalues, hjump, hzero⟩

#print axioms a
#print axioms lower
#print axioms upper
#print axioms result

end D5.S1.Deficit.Beatty.KimberlingRoundedHalfRootTwoDifference
