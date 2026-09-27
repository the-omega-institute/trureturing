/- GID: D5/S1/Recurrence/Sun/VStrict
   generality: G
   mirror-B: D5/B/S1/Recurrence/Sun/VStrict
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The strict lowercase v Turan inequality on its full closed domain. -/

import D5.S1.Recurrence.Sun.VTail

namespace D5.S1.Recurrence.Sun.VStrict

open D5.S1.Recurrence.Sun.Sequences
open D5.S1.Recurrence.Sun.VTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The second strict clause of Sun's Conjecture 5.2, including `x = -1/8`. -/
theorem v_strict_turan (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x ≤ -(1 / 8)) :
    v x n ^ 2 > v x (n - 1) * v x (n + 1) := by
  let t : ℝ := -x
  have ht : 1 / 8 ≤ t := by dsimp [t]; linarith
  let R : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * v (-t) j
  have hR0 : R 0 = 1 := by simp [R, v]
  have hRrec (j : ℕ) :
      ((j : ℝ) + 2) ^ 3 * R (j + 2) =
        (2 * ((j : ℝ) + 1) + 1) *
          (t - ((j : ℝ) + 1) * ((j : ℝ) + 2)) * R (j + 1) -
            ((j : ℝ) + 1) ^ 3 * R j := by
    simp [R, v, pow_succ]
    field_simp
    ring
  have hpair : ∀ j : ℕ, ¬ (R j = 0 ∧ R (j + 1) = 0) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        cases j with
        | zero => simpa [hR0] using (show (1 : ℝ) ≠ 0 by norm_num)
        | succ k =>
            rintro ⟨hk1, hk2⟩
            have hk0 : R k = 0 := by
              have hr := hRrec k
              rw [hk1, hk2] at hr
              have hpos : 0 < ((k : ℝ) + 1) ^ 3 := by positivity
              nlinarith
            exact ih k (by omega) ⟨hk0, hk1⟩
  let m : ℝ := (n : ℝ) * ((n : ℝ) + 1)
  let D : ℝ := 4 * m + 1
  let r : ℝ := 2 * m * Real.sqrt m / Real.sqrt D
  let L : ℝ := m - r
  let U : ℝ := m + r
  let T : ℝ := m - 2 * (n : ℝ) ^ 3 /
    Real.sqrt (4 * (n : ℝ) ^ 2 - 1)
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hm : 2 ≤ m := by dsimp [m]; nlinarith
  have hD : 0 < D := by dsimp [D]; linarith
  have hrootm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by linarith)
  have hrootD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrsq : D * r ^ 2 = 4 * m ^ 3 := by
    dsimp [r]
    rw [div_pow, mul_pow, Real.sq_sqrt hD.le, Real.sq_sqrt (by linarith : 0 ≤ m)]
    field_simp [hD.ne']
    ring
  have hedge : 4 * m ^ 3 - (m - 1 / 8) ^ 2 * D =
      (12 * m - 1) / 64 := by dsimp [D]; ring
  have hL : L < 1 / 8 := by
    have hpoly : 0 < 4 * m ^ 3 - (m - 1 / 8) ^ 2 * D := by
      rw [hedge]
      linarith
    have hsquare : (m - 1 / 8) ^ 2 < r ^ 2 := by
      have hmul : (m - 1 / 8) ^ 2 * D < r ^ 2 * D := by
        nlinarith only [hpoly, hrsq]
      exact lt_of_mul_lt_mul_right hmul hD.le
    have hlt : m - 1 / 8 < r := by
      have hmsmall : 0 ≤ m - 1 / 8 := by linarith only [hm]
      nlinarith only [hrpos, hsquare, hmsmall]
    dsimp [L]
    linarith
  have hT : T < m := by
    have harg : 0 < 4 * (n : ℝ) ^ 2 - 1 := by nlinarith
    have hroot : 0 < Real.sqrt (4 * (n : ℝ) ^ 2 - 1) :=
      Real.sqrt_pos.2 harg
    dsimp [T]
    have hquot : 0 < 2 * (n : ℝ) ^ 3 /
        Real.sqrt (4 * (n : ℝ) ^ 2 - 1) := by positivity
    linarith
  have hU : m < U := by dsimp [U]; linarith
  have hdet : 0 < R n ^ 2 - R (n - 1) * R (n + 1) := by
    by_cases htail : T ≤ t
    · have ht' : (n : ℝ) * ((n : ℝ) + 1) -
          2 * (n : ℝ) ^ 3 / Real.sqrt (4 * (n : ℝ) ^ 2 - 1) ≤ t := by
        simpa [T, m] using htail
      exact v_tail_strict n hn t ht'
    · have hlocal : t < T := lt_of_not_ge htail
      have htm : t < m := lt_trans hlocal hT
      have hleft : m - t < r := by
        dsimp [L] at hL
        linarith
      have hright : t < U := lt_trans htm hU
      have hgap : (m - t) ^ 2 < r ^ 2 := by
        nlinarith only [hleft, htm, hrpos]
      have hdisc :
          0 < 4 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ 3 -
            ((2 * (n : ℝ) + 1) * (t - m)) ^ 2 := by
        have hmul : 0 < D * (r ^ 2 - (m - t) ^ 2) :=
          mul_pos hD (by linarith)
        have heq :
            D * (r ^ 2 - (m - t) ^ 2) =
              4 * ((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ 3 -
                ((2 * (n : ℝ) + 1) * (t - m)) ^ 2 := by
          dsimp [D, m] at *
          nlinarith [hrsq]
        rw [← heq]
        exact hmul
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      subst n
      have hquad_id :
          4 * ((k : ℝ) + 2) ^ 3 *
              (((k : ℝ) + 2) ^ 3 *
                (R (k + 1) ^ 2 - R k * R (k + 2))) =
            (2 * ((k : ℝ) + 2) ^ 3 * R (k + 1) -
              (2 * ((k : ℝ) + 1) + 1) *
                (t - ((k : ℝ) + 1) * ((k : ℝ) + 2)) * R k) ^ 2 +
              (4 * ((k : ℝ) + 2) ^ 3 * ((k : ℝ) + 1) ^ 3 -
                ((2 * ((k : ℝ) + 1) + 1) *
                  (t - ((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ 2) * R k ^ 2 := by
        calc
          _ = 4 * ((k : ℝ) + 2) ^ 3 *
              (((k : ℝ) + 2) ^ 3 * R (k + 1) ^ 2 -
                (2 * ((k : ℝ) + 1) + 1) *
                  (t - ((k : ℝ) + 1) * ((k : ℝ) + 2)) * R k * R (k + 1) +
                  ((k : ℝ) + 1) ^ 3 * R k ^ 2) := by
              linear_combination -4 * ((k : ℝ) + 2) ^ 3 * R k * hRrec k
          _ = _ := by ring
      have hdisc' :
          0 < 4 * ((k : ℝ) + 2) ^ 3 * ((k : ℝ) + 1) ^ 3 -
              ((2 * ((k : ℝ) + 1) + 1) *
                (t - ((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ 2 := by
        dsimp [m] at hdisc
        convert hdisc using 1 <;> push_cast <;> ring
      have hnonzero : R k ≠ 0 ∨ R (k + 1) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hpair k h
      have hrhs : 0 <
          (2 * ((k : ℝ) + 2) ^ 3 * R (k + 1) -
            (2 * ((k : ℝ) + 1) + 1) *
              (t - ((k : ℝ) + 1) * ((k : ℝ) + 2)) * R k) ^ 2 +
            (4 * ((k : ℝ) + 2) ^ 3 * ((k : ℝ) + 1) ^ 3 -
              ((2 * ((k : ℝ) + 1) + 1) *
                (t - ((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ 2) * R k ^ 2 := by
        rcases hnonzero with hk0 | hk1
        · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
            (mul_pos hdisc' (sq_pos_of_ne_zero hk0))
        · by_cases hk0 : R k = 0
          · rw [hk0]
            have hs : 0 < (2 * ((k : ℝ) + 2) ^ 3 * R (k + 1)) ^ 2 :=
              sq_pos_of_ne_zero (mul_ne_zero (by positivity) hk1)
            simpa using hs
          · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
              (mul_pos hdisc' (sq_pos_of_ne_zero hk0))
      have hpositive : 0 < R (k + 1) ^ 2 - R k * R (k + 2) := by
        have hfac : 0 < 4 * ((k : ℝ) + 2) ^ 3 * ((k : ℝ) + 2) ^ 3 := by
          positivity
        have hscaled : 0 <
            (4 * ((k : ℝ) + 2) ^ 3 * ((k : ℝ) + 2) ^ 3) *
              (R (k + 1) ^ 2 - R k * R (k + 2)) := by
          calc
            _ = 4 * ((k : ℝ) + 2) ^ 3 *
                (((k : ℝ) + 2) ^ 3 *
                  (R (k + 1) ^ 2 - R k * R (k + 2))) := by ring
            _ = _ := hquad_id
            _ > 0 := hrhs
        exact pos_of_mul_pos_right hscaled hfac.le
      simpa [Nat.succ_eq_add_one] using hpositive
  have htranslate : R n ^ 2 - R (n - 1) * R (n + 1) =
      v x n ^ 2 - v x (n - 1) * v x (n + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hkprev : (k + 1 : ℕ) - 1 = k := by omega
    have hknext : (k + 1 : ℕ) + 1 = k + 2 := by omega
    have hsgn : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
      rw [← pow_mul, show (k + 1) * 2 = 2 * (k + 1) by omega, pow_mul]
      norm_num
    have hneighbors : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 2) = 1 := by
      rw [← pow_add, show k + (k + 2) = 2 * (k + 1) by omega, pow_mul]
      norm_num
    have htx : -t = x := by dsimp [t]; ring
    simp only [Nat.succ_eq_add_one, hkprev, hknext, R, htx]
    rw [mul_pow, hsgn, one_mul]
    calc
      _ = v x (k + 1) ^ 2 -
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 2)) *
            (v x k * v x (k + 2)) := by ring
      _ = _ := by rw [hneighbors, one_mul]
  rw [htranslate] at hdet
  exact sub_pos.mp hdet

#print axioms v_strict_turan

end D5.S1.Recurrence.Sun.VStrict
