/- GID: D5/S1/Recurrence/Sun/GStrict
   generality: G
   mirror-B: D5/B/S1/Recurrence/Sun/GStrict
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The strict lowercase g Turan inequality on its full closed domain. -/

import D5.S1.Recurrence.Sun.GEndpoint
import D5.S1.Recurrence.Turan.StrictlyIncreasingTail

namespace D5.S1.Recurrence.Sun.GStrict

open D5.S1.Recurrence.Sun.Sequences
open D5.S1.Recurrence.Sun.GEndpoint
open D5.S1.Recurrence.Turan.StrictlyIncreasingTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The first strict clause of Sun's Conjecture 5.2, including `x = -1`. -/
theorem g_strict_turan (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x ≤ -1) :
    g x n ^ 2 > g x (n - 1) * g x (n + 1) := by
  let t : ℝ := -(x + 1) / 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hx' : x = -2 * t - 1 := by dsimp [t]; ring
  let P : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * g (-2 * t - 1) k
  have hP0 : P 0 = 1 := by simp [P, g]
  have hP1 : P 1 = t := by simp [P, g]; ring
  have hrec (k : ℕ) :
      ((k : ℝ) + 2) ^ 2 * P (k + 2) =
        (t - 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) * P (k + 1) -
          ((k : ℝ) + 1) ^ 2 * P k := by
    simp [P, g, pow_succ]
    field_simp
    ring
  have hpair : ∀ k : ℕ, ¬ (P k = 0 ∧ P (k + 1) = 0) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        cases k with
        | zero => simpa [hP0] using (show (1 : ℝ) ≠ 0 by norm_num)
        | succ j =>
            rintro ⟨hj1, hj2⟩
            have hj0 : P j = 0 := by
              have hr := hrec j
              rw [hj1, hj2] at hr
              have hpos : 0 < ((j : ℝ) + 1) ^ 2 := by positivity
              nlinarith
            exact ih j (by omega) ⟨hj0, hj1⟩
  have hdet (m : ℕ) (hm : 1 ≤ m) :
      0 < P m ^ 2 - P (m - 1) * P (m + 1) := by
    by_cases hzero : t = 0
    · have hx0 : x = -1 := by rw [hx']; rw [hzero]; ring
      have hs (k : ℕ) : (-1 : ℝ) ^ k * g (-1) k = P k := by
        simp [P, hzero]
      have hraw := g_endpoint_strict m hm
      have heq : P m ^ 2 - P (m - 1) * P (m + 1) =
          g (-1) m ^ 2 - g (-1) (m - 1) * g (-1) (m + 1) := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        have hjprev : (j + 1 : ℕ) - 1 = j := by omega
        have hjnext : (j + 1 : ℕ) + 1 = j + 2 := by omega
        simp only [Nat.succ_eq_add_one, hjprev, hjnext, P, hzero]
        have hsgn : ((-1 : ℝ) ^ (j + 1)) ^ 2 = 1 := by
          rw [← pow_mul, show (j + 1) * 2 = 2 * (j + 1) by omega, pow_mul]
          norm_num
        have hneighbors : (-1 : ℝ) ^ j * (-1 : ℝ) ^ (j + 2) = 1 := by
          rw [← pow_add, show j + (j + 2) = 2 * (j + 1) by omega, pow_mul]
          norm_num
        rw [mul_pow, hsgn, one_mul]
        calc
          _ = g (-1) (j + 1) ^ 2 -
              ((-1 : ℝ) ^ j * (-1 : ℝ) ^ (j + 2)) *
                (g (-1) j * g (-1) (j + 2)) := by ring
          _ = _ := by rw [hneighbors, one_mul]
      rw [heq]
      simpa [Nat.succ_eq_add_one] using (sub_pos.mpr hraw)
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
      by_cases hlocal : t < 2 * (m : ℝ)
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        have hcoef :
            0 < 4 * ((k : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) ^ 2 -
              (t - 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ^ 2 := by
          have hbound : t < 2 * ((k : ℝ) + 1) := by simpa using hlocal
          have hfactor : 0 < t *
              (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2) - t) := by
            apply mul_pos htpos
            nlinarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
          nlinarith [hfactor]
        have hquad_id :
            4 * ((k : ℝ) + 2) ^ 2 *
                (((k : ℝ) + 2) ^ 2 *
                  (P (k + 1) ^ 2 - P k * P (k + 2))) =
              (2 * ((k : ℝ) + 2) ^ 2 * P (k + 1) -
                (t - 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) * P k) ^ 2 +
              (4 * ((k : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) ^ 2 -
                (t - 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ^ 2) * P k ^ 2 := by
          calc
            _ = 4 * ((k : ℝ) + 2) ^ 2 *
                (((k : ℝ) + 2) ^ 2 * P (k + 1) ^ 2 -
                  (t - 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) * P k * P (k + 1) +
                  ((k : ℝ) + 1) ^ 2 * P k ^ 2) := by
                    linear_combination -4 * ((k : ℝ) + 2) ^ 2 * P k * hrec k
            _ = _ := by ring
        have hnonzero : P k ≠ 0 ∨ P (k + 1) ≠ 0 := by
          by_contra h
          push_neg at h
          exact hpair k h
        have hrhs : 0 <
            (2 * ((k : ℝ) + 2) ^ 2 * P (k + 1) -
                (t - 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) * P k) ^ 2 +
              (4 * ((k : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) ^ 2 -
                (t - 2 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) ^ 2) * P k ^ 2 := by
          rcases hnonzero with hk | hk1
          · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hcoef (sq_pos_of_ne_zero hk))
          · by_cases hk : P k = 0
            · rw [hk]
              have hs : 0 < (2 * ((k : ℝ) + 2) ^ 2 * P (k + 1)) ^ 2 :=
                sq_pos_of_ne_zero (mul_ne_zero (by positivity) hk1)
              simpa using hs
            · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hcoef (sq_pos_of_ne_zero hk))
        have hfactor : 0 < 4 * ((k : ℝ) + 2) ^ 4 := by positivity
        have hpositive : 0 < P (k + 1) ^ 2 - P k * P (k + 2) := by
          nlinarith [hquad_id]
        simpa [Nat.succ_eq_add_one] using hpositive
      · have htail : 2 * (m : ℝ) ≤ t := le_of_not_gt hlocal
        let a : ℕ → ℝ := fun j => (j : ℝ) ^ 2
        let b : ℕ → ℝ := fun j => 2 * (j : ℝ) * ((j : ℝ) + 1)
        let q := orthonormal a b t
        have ha0 : a 0 = 0 := by norm_num [a]
        have ha : StrictMono a := by
          apply strictMono_nat_of_lt_succ
          intro j
          dsimp [a]
          have hj : 0 ≤ (j : ℝ) := by positivity
          push_cast
          nlinarith
        have hb : Monotone b := by
          apply monotone_nat_of_le_succ
          intro j
          dsimp [b]
          push_cast
          nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
        have hident : ∀ j : ℕ, P j = q j := by
          intro j
          induction j using Nat.twoStepInduction with
          | zero => simp [hP0, q, orthonormal]
          | one => simp [hP1, q, orthonormal, a, b]
          | more j ih0 ih1 =>
              have hpos : 0 < a (j + 2) := by dsimp [a]; positivity
              have hq : a (j + 2) * q (j + 2) =
                  (t - b (j + 1)) * q (j + 1) - a (j + 1) * q j := by
                dsimp [q]
                rw [show orthonormal a b t (j + 2) =
                    ((t - b (j + 1)) * orthonormal a b t (j + 1) -
                      a (j + 1) * orthonormal a b t j) / a (j + 2) by rfl]
                field_simp [hpos.ne']
              rw [← ih0, ← ih1] at hq
              dsimp [a, b] at hq
              push_cast at hq
              have hp := hrec j
              nlinarith
        have hthreshold : b m - 2 * a m ≤ t := by
          dsimp [b, a]
          nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
        have hweighted := weighted_turan_nonneg_of_strict_mono
          a b t ha0 ha hb m hm hthreshold
        change 0 ≤ q m ^ 2 - (a (m + 1) / a m) * q (m - 1) * q (m + 1)
          at hweighted
        rw [← hident m, ← hident (m - 1), ← hident (m + 1)] at hweighted
        have ham : 0 < a m := by dsimp [a]; positivity
        have hweight : 1 < a (m + 1) / a m := by
          apply (one_lt_div ham).2
          exact ha (by omega)
        let z := P (m - 1) * P (m + 1)
        have hprev : m - 1 + 1 = m := by omega
        have hnz : z = 0 → P m ≠ 0 := by
          intro hz hp
          have hz' : P (m - 1) = 0 ∨ P (m + 1) = 0 :=
            mul_eq_zero.mp hz
          rcases hz' with hz0 | hz1
          · exact hpair (m - 1) (by simpa [hprev] using And.intro hz0 hp)
          · exact hpair m ⟨hp, hz1⟩
        have hweighted' : 0 ≤ P m ^ 2 - (a (m + 1) / a m) * z := by
          calc
            _ = P m ^ 2 - (a (m + 1) / a m) * P (m - 1) * P (m + 1) := by
              dsimp [z]
              ring
            _ ≥ 0 := hweighted
        change 0 < P m ^ 2 - z
        rcases lt_trichotomy z 0 with hz | hz | hz
        · nlinarith [sq_nonneg (P m)]
        · have hp : 0 < P m ^ 2 := sq_pos_of_ne_zero (hnz hz)
          nlinarith [hweighted']
        · have hgain : 0 < (a (m + 1) / a m - 1) * z :=
            mul_pos (by linarith) hz
          nlinarith [hweighted']
  have htranslate :
      P n ^ 2 - P (n - 1) * P (n + 1) =
        g x n ^ 2 - g x (n - 1) * g x (n + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hkprev : (k + 1 : ℕ) - 1 = k := by omega
    have hknext : (k + 1 : ℕ) + 1 = k + 2 := by omega
    have hsgn : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
      rw [← pow_mul, show (k + 1) * 2 = 2 * (k + 1) by omega, pow_mul]
      norm_num
    have hneighbors : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 2) = 1 := by
      rw [← pow_add, show k + (k + 2) = 2 * (k + 1) by omega, pow_mul]
      norm_num
    simp only [Nat.succ_eq_add_one, hkprev, hknext, P, ← hx']
    rw [mul_pow, hsgn, one_mul]
    calc
      _ = g x (k + 1) ^ 2 -
          ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 2)) *
            (g x k * g x (k + 2)) := by ring
      _ = _ := by rw [hneighbors, one_mul]
  have hd := hdet n hn
  rw [htranslate] at hd
  exact sub_pos.mp hd

#print axioms g_strict_turan

end D5.S1.Recurrence.Sun.GStrict
