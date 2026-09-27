/- GID: D5/S1/Recurrence/Sun/VTail
   generality: G
   mirror-B: D5/B/S1/Recurrence/Sun/VTail
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Radical normalization and strict Turan inequality for Sun's v right tail. -/

import D5.S1.Recurrence.Sun.Sequences
import D5.S1.Recurrence.Turan.StrictlyIncreasingTail

namespace D5.S1.Recurrence.Sun.VTail

open D5.S1.Recurrence.Sun.Sequences
open D5.S1.Recurrence.Turan.StrictlyIncreasingTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The strict normalized Krasikov tail for the lowercase `v` sequence. -/
theorem v_tail_strict (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : (n : ℝ) * ((n : ℝ) + 1) -
      2 * (n : ℝ) ^ 3 / Real.sqrt (4 * (n : ℝ) ^ 2 - 1) ≤ t) :
    0 < ((-1 : ℝ) ^ n * v (-t) n) ^ 2 -
      ((-1 : ℝ) ^ (n - 1) * v (-t) (n - 1)) *
        ((-1 : ℝ) ^ (n + 1) * v (-t) (n + 1)) := by
  let R : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * v (-t) j
  let a : ℕ → ℝ := fun j =>
    if j = 0 then 0 else (j : ℝ) ^ 3 / Real.sqrt (4 * (j : ℝ) ^ 2 - 1)
  let b : ℕ → ℝ := fun j => (j : ℝ) * ((j : ℝ) + 1)
  let c : ℕ → ℝ := fun j =>
    if j = 0 then 1 else Real.sqrt ((2 * (j : ℝ) - 1) / (2 * (j : ℝ) + 1))
  let d : ℕ → ℝ := fun j => 1 / Real.sqrt (2 * (j : ℝ) + 1)
  let q : ℕ → ℝ := fun j => Real.sqrt (2 * (j : ℝ) + 1) * R j
  have hR0 : R 0 = 1 := by simp [R, v]
  have hR1 : R 1 = t := by simp [R, v]
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
  have hrad (j : ℕ) (hj : 1 ≤ j) :
      0 < 4 * (j : ℝ) ^ 2 - 1 := by
    have hjr : 1 ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  have hroot (j : ℕ) (hj : 1 ≤ j) :
      0 < Real.sqrt (4 * (j : ℝ) ^ 2 - 1) :=
    Real.sqrt_pos.2 (hrad j hj)
  have hsplit (j : ℕ) (hj : 1 ≤ j) :
      Real.sqrt (4 * (j : ℝ) ^ 2 - 1) =
        Real.sqrt (2 * (j : ℝ) - 1) * Real.sqrt (2 * (j : ℝ) + 1) := by
    have hjr : 1 ≤ (j : ℝ) := by exact_mod_cast hj
    rw [← Real.sqrt_mul (by linarith : 0 ≤ 2 * (j : ℝ) - 1)]
    congr 1
    ring
  have haroot (j : ℕ) (hj : 1 ≤ j) :
      a j * Real.sqrt (2 * (j : ℝ) + 1) =
        (j : ℝ) ^ 3 / Real.sqrt (2 * (j : ℝ) - 1) := by
    have hjr : 1 ≤ (j : ℝ) := by exact_mod_cast hj
    have hspos : 0 < Real.sqrt (2 * (j : ℝ) - 1) :=
      Real.sqrt_pos.2 (by linarith)
    have htpos : 0 < Real.sqrt (2 * (j : ℝ) + 1) :=
      Real.sqrt_pos.2 (by linarith)
    simp only [a, if_neg (by omega : j ≠ 0)]
    rw [hsplit j hj]
    field_simp [hspos.ne', htpos.ne']
  have ha0 : a 0 = 0 := by simp [a]
  have ha_pos (j : ℕ) (hj : 1 ≤ j) : 0 < a j := by
    simp only [a, if_neg (by omega : j ≠ 0)]
    exact div_pos (by positivity) (hroot j hj)
  have ha : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro j
    by_cases hj : j = 0
    · subst j
      simpa [ha0] using ha_pos 1 (by omega)
    · have hj1 : 1 ≤ j := by omega
      have hj2 : 1 ≤ j + 1 := by omega
      have hd1 := hrad j hj1
      have hd2 := hrad (j + 1) hj2
      have hsquare (k : ℕ) (hk : 1 ≤ k) :
          (a k) ^ 2 = (k : ℝ) ^ 6 / (4 * (k : ℝ) ^ 2 - 1) := by
        simp only [a, if_neg (by omega : k ≠ 0)]
        rw [div_pow, Real.sq_sqrt (hrad k hk).le]
        ring
      have hpoly :
          (j + 1 : ℕ) ^ (6 : ℕ) * (4 * (j : ℝ) ^ 2 - 1) -
            (j : ℝ) ^ 6 * (4 * (j + 1 : ℕ) ^ 2 - 1) > 0 := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        push_cast
        norm_num only [Nat.cast_add, Nat.cast_one]
        have heq :
            ((k : ℝ) + 2) ^ 6 * (4 * ((k : ℝ) + 1) ^ 2 - 1) -
                ((k : ℝ) + 1) ^ 6 * (4 * ((k : ℝ) + 2) ^ 2 - 1) =
              16 * (k : ℝ) ^ 7 + 168 * (k : ℝ) ^ 6 +
              746 * (k : ℝ) ^ 5 + 1815 * (k : ℝ) ^ 4 +
              2604 * (k : ℝ) ^ 3 + 2187 * (k : ℝ) ^ 2 +
              982 * (k : ℝ) + 177 := by ring
        calc
          _ = 16 * (k : ℝ) ^ 7 + 168 * (k : ℝ) ^ 6 +
                746 * (k : ℝ) ^ 5 + 1815 * (k : ℝ) ^ 4 +
                2604 * (k : ℝ) ^ 3 + 2187 * (k : ℝ) ^ 2 +
                982 * (k : ℝ) + 177 := by convert heq using 1 <;> ring
          _ > 0 := by positivity
      have hsquares : (a j) ^ 2 < (a (j + 1)) ^ 2 := by
        rw [hsquare j hj1, hsquare (j + 1) hj2]
        exact (div_lt_div_iff₀ hd1 hd2).2 (by nlinarith [hpoly])
      nlinarith [ha_pos j hj1, ha_pos (j + 1) hj2]
  have hb : Monotone b := by
    apply monotone_nat_of_le_succ
    intro j
    dsimp [b]
    push_cast
    nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
  have hd0 : d 0 = 1 := by norm_num [d]
  have hdpos (j : ℕ) : 0 < d j := by
    dsimp [d]
    exact div_pos (by norm_num) (Real.sqrt_pos.2 (by positivity))
  have hdsucc (j : ℕ) : d (j + 1) = c (j + 1) * d j := by
    have hj : 0 < 2 * (j : ℝ) + 1 := by positivity
    have hj' : 0 < 2 * (j : ℝ) + 3 := by positivity
    have hrootj : 0 < Real.sqrt (2 * (j : ℝ) + 1) := Real.sqrt_pos.2 hj
    have hrootj' : 0 < Real.sqrt (2 * (j : ℝ) + 3) := Real.sqrt_pos.2 hj'
    simp only [d, c, if_neg (by omega : j + 1 ≠ 0)]
    push_cast
    have hnum : 2 * ((j : ℝ) + 1) - 1 = 2 * (j : ℝ) + 1 := by ring
    have hden : 2 * ((j : ℝ) + 1) + 1 = 2 * (j : ℝ) + 3 := by ring
    rw [hnum, hden]
    rw [Real.sqrt_div hj.le]
    field_simp [hrootj.ne', hrootj'.ne']
  have hcroot (j : ℕ) :
      c (j + 1) * Real.sqrt (2 * (((j + 1 : ℕ) : ℝ)) + 1) =
        Real.sqrt (2 * (j : ℝ) + 1) := by
    have hp : 0 < Real.sqrt (2 * (j : ℝ) + 1) :=
      Real.sqrt_pos.2 (by positivity)
    have hp' : 0 < Real.sqrt (2 * (j : ℝ) + 3) :=
      Real.sqrt_pos.2 (by positivity)
    simp only [c, if_neg (by omega : j + 1 ≠ 0)]
    push_cast
    have hnum : 2 * ((j : ℝ) + 1) - 1 = 2 * (j : ℝ) + 1 := by ring
    have hden : 2 * ((j : ℝ) + 1) + 1 = 2 * (j : ℝ) + 3 := by ring
    rw [hnum, hden, Real.sqrt_div (by positivity : 0 ≤ 2 * (j : ℝ) + 1)]
    field_simp [hp.ne', hp'.ne']
  have hdroot : ∀ j : ℕ, d j * Real.sqrt (2 * (j : ℝ) + 1) = 1 := by
    intro j
    induction j with
    | zero => norm_num [hd0]
    | succ j ih =>
        rw [hdsucc j]
        calc
          _ = d j * (c (j + 1) *
              Real.sqrt (2 * (((j + 1 : ℕ) : ℝ)) + 1)) := by ring
          _ = d j * Real.sqrt (2 * (j : ℝ) + 1) := by rw [hcroot j]
          _ = 1 := ih
  have hRscale (j : ℕ) : R j = d j * q j := by
    change R j = d j * (Real.sqrt (2 * (j : ℝ) + 1) * R j)
    rw [← mul_assoc, hdroot j, one_mul]
  have hq0 : q 0 = 1 := by simp [q, hR0]
  have hq1 : q 1 = (t - b 0) / a 1 := by
    have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    simp only [q, hR1]
    simp [a, b]
    ring
  have hqrec (j : ℕ) :
      a (j + 2) * q (j + 2) =
        (t - b (j + 1)) * q (j + 1) - a (j + 1) * q j := by
    have hs := haroot (j + 2) (by omega)
    have hrootj : 0 < Real.sqrt (2 * (j : ℝ) + 3) :=
      Real.sqrt_pos.2 (by positivity)
    have hrootprev : 0 < Real.sqrt (2 * (j : ℝ) + 1) :=
      Real.sqrt_pos.2 (by positivity)
    have hroot_sq : Real.sqrt (2 * (j : ℝ) + 3) ^ 2 =
        2 * (j : ℝ) + 3 := Real.sq_sqrt (by positivity)
    have hs' : a (j + 1) * Real.sqrt (2 * (j : ℝ) + 1) =
        ((j : ℝ) + 1) ^ 3 / Real.sqrt (2 * (j : ℝ) + 3) := by
      have hj : j + 1 ≠ 0 := by omega
      simp only [a, if_neg hj]
      rw [hsplit (j + 1) (by omega)]
      push_cast
      have hnum : 2 * ((j : ℝ) + 1) - 1 = 2 * (j : ℝ) + 1 := by ring
      have hden : 2 * ((j : ℝ) + 1) + 1 = 2 * (j : ℝ) + 3 := by ring
      rw [hnum, hden]
      field_simp [hrootprev.ne', hrootj.ne']
    have hnormalize :
        ((j : ℝ) + 2) ^ 3 / Real.sqrt (2 * (j : ℝ) + 3) * R (j + 2) =
          (t - ((j : ℝ) + 1) * ((j : ℝ) + 2)) *
              Real.sqrt (2 * (j : ℝ) + 3) * R (j + 1) -
            ((j : ℝ) + 1) ^ 3 / Real.sqrt (2 * (j : ℝ) + 3) * R j := by
      apply (mul_left_inj' hrootj.ne').mp
      field_simp [hrootj.ne']
      simp only [mul_comm (j : ℝ) (2 : ℝ)]
      linear_combination hRrec j -
        (t - ((j : ℝ) + 1) * ((j : ℝ) + 2)) * R (j + 1) * hroot_sq
    have hnextroot : Real.sqrt (2 * ((j + 2 : ℕ) : ℝ) - 1) =
        Real.sqrt (2 * (j : ℝ) + 3) := by
      congr 1
      push_cast
      ring
    calc
      _ = (a (j + 2) * Real.sqrt (2 * ((j + 2 : ℕ) : ℝ) + 1)) *
            R (j + 2) := by dsimp [q]; ring
      _ = ((j : ℝ) + 2) ^ 3 / Real.sqrt (2 * (j : ℝ) + 3) * R (j + 2) := by
        rw [hs, hnextroot]
        push_cast
        rfl
      _ = (t - ((j : ℝ) + 1) * ((j : ℝ) + 2)) *
              Real.sqrt (2 * (j : ℝ) + 3) * R (j + 1) -
            ((j : ℝ) + 1) ^ 3 / Real.sqrt (2 * (j : ℝ) + 3) * R j := hnormalize
      _ = _ := by
        change (t - ((j : ℝ) + 1) * ((j : ℝ) + 2)) *
            Real.sqrt (2 * (j : ℝ) + 3) * R (j + 1) -
              ((j : ℝ) + 1) ^ 3 / Real.sqrt (2 * (j : ℝ) + 3) * R j =
          (t - b (j + 1)) * q (j + 1) - a (j + 1) * q j
        have hright : a (j + 1) * q j =
            ((j : ℝ) + 1) ^ 3 / Real.sqrt (2 * (j : ℝ) + 3) * R j := by
          change a (j + 1) * (Real.sqrt (2 * (j : ℝ) + 1) * R j) = _
          calc
            _ = (a (j + 1) * Real.sqrt (2 * (j : ℝ) + 1)) * R j := by ring
            _ = _ := by rw [hs']
        rw [hright]
        dsimp [q, b]
        push_cast
        ring
  have hident : ∀ j : ℕ, q j = orthonormal a b t j := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => simp [hq0, orthonormal]
    | one => simp [hq1, orthonormal]
    | more j ih0 ih1 =>
        have hp := ha_pos (j + 2) (by omega)
        have hr := hqrec j
        rw [ih0, ih1] at hr
        have hc : orthonormal a b t (j + 2) =
            ((t - b (j + 1)) * orthonormal a b t (j + 1) -
              a (j + 1) * orthonormal a b t j) / a (j + 2) := by rfl
        rw [hc]
        apply (eq_div_iff hp.ne').2
        simpa [mul_comm] using hr
  have hweight : 1 <
      ((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
        ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1)) := by
    have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : 0 < (n : ℝ) ^ 3 * (2 * (n : ℝ) + 1) := by positivity
    apply (one_lt_div hden).2
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    push_cast
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hid :
        ((k : ℝ) + 2) ^ 3 * (2 * ((k : ℝ) + 1) - 1) -
            ((k : ℝ) + 1) ^ 3 * (2 * ((k : ℝ) + 1) + 1) =
          4 * (k : ℝ) ^ 3 + 15 * (k : ℝ) ^ 2 + 17 * (k : ℝ) + 5 := by ring
    have hpoly : 0 <
        ((k : ℝ) + 2) ^ 3 * (2 * ((k : ℝ) + 1) - 1) -
          ((k : ℝ) + 1) ^ 3 * (2 * ((k : ℝ) + 1) + 1) := by
      rw [hid]
      positivity
    nlinarith [hpoly]
  have hthreshold : b n - 2 * a n ≤ t := by
    simp only [a, b, if_neg (by omega : n ≠ 0)]
    convert ht using 1 <;> ring
  have hweighted := weighted_turan_nonneg_of_strict_mono
    a b t ha0 ha hb n hn hthreshold
  rw [← hident n, ← hident (n - 1), ← hident (n + 1)] at hweighted
  have htransport :
      (a (n + 1) / a n) * q (n - 1) * q (n + 1) =
        (2 * (n : ℝ) + 1) *
          (((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
            ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1))) *
              (R (n - 1) * R (n + 1)) := by
    have hn0 : n ≠ 0 := by omega
    have hn1 : 1 ≤ n + 1 := by omega
    have hnroot := hroot n hn
    have hnroot' := hroot (n + 1) hn1
    have hs := hsplit n hn
    have hs' := hsplit (n + 1) hn1
    have hprev : 2 * ((n - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) - 1 := by
      have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]
        norm_num
      rw [hsub]
      ring
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hsq : Real.sqrt (2 * (n : ℝ) - 1) ^ 2 =
        2 * (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
    have hnextroot : Real.sqrt (2 * (((n + 1 : ℕ) : ℝ)) - 1) =
        Real.sqrt (2 * (n : ℝ) + 1) := by
      congr 1
      push_cast
      ring
    simp only [q, a, if_neg hn0, if_neg (by omega : n + 1 ≠ 0)]
    rw [hs, hs', hprev, hnextroot]
    push_cast
    field_simp [hnroot.ne', hnroot'.ne', Real.sqrt_pos.2 (by linarith :
      0 < 2 * (n : ℝ) - 1) |>.ne', Real.sqrt_pos.2 (by positivity :
      0 < 2 * (n : ℝ) + 1) |>.ne', Real.sqrt_pos.2 (by positivity :
      0 < 2 * (n : ℝ) + 3) |>.ne']
    have hsq' : Real.sqrt ((n : ℝ) * 2 - 1) ^ 2 =
        (n : ℝ) * 2 - 1 := by simpa [mul_comm] using hsq
    rw [hsq']
  have hwR : 0 ≤ R n ^ 2 -
      (((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
        ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1))) * R (n - 1) * R (n + 1) := by
    have hd2pos : 0 < d n ^ 2 := sq_pos_of_pos (hdpos n)
    have hd2factor : d n ^ 2 * (2 * (n : ℝ) + 1) = 1 := by
      dsimp [d]
      rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (n : ℝ) + 1)]
      field_simp
    have hmain : d n ^ 2 * q n ^ 2 = R n ^ 2 := by
      rw [hRscale n]
      ring
    have hweighted' : 0 ≤ q n ^ 2 -
        (a (n + 1) / a n) * q (n - 1) * q (n + 1) := hweighted
    have hscaled := mul_nonneg hd2pos.le hweighted'
    have htransport' : d n ^ 2 *
        (q n ^ 2 - (a (n + 1) / a n) * q (n - 1) * q (n + 1)) =
          R n ^ 2 -
            (((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
              ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1))) *
                R (n - 1) * R (n + 1) := by
      calc
        _ = d n ^ 2 * q n ^ 2 -
            d n ^ 2 * ((a (n + 1) / a n) * q (n - 1) * q (n + 1)) := by
              ring
        _ = R n ^ 2 - d n ^ 2 *
            ((2 * (n : ℝ) + 1) *
              (((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
                ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1))) *
                  (R (n - 1) * R (n + 1))) := by rw [hmain, htransport]
        _ = _ := by
          linear_combination -
            ((((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
              ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1))) *
                (R (n - 1) * R (n + 1))) * hd2factor
    rw [htransport'] at hscaled
    exact hscaled
  have hnz : R (n - 1) * R (n + 1) = 0 → R n ≠ 0 := by
    intro hz hr
    rcases mul_eq_zero.mp hz with hl | hr'
    · exact hpair (n - 1) (by simpa [show n - 1 + 1 = n by omega] using And.intro hl hr)
    · exact hpair n ⟨hr, hr'⟩
  change 0 < R n ^ 2 - R (n - 1) * R (n + 1)
  let z := R (n - 1) * R (n + 1)
  have hwR' : 0 ≤ R n ^ 2 -
      (((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
        ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1))) * z := by
    dsimp [z]
    nlinarith [hwR]
  change 0 < R n ^ 2 - z
  rcases lt_trichotomy z 0 with hz | hz | hz
  · nlinarith [sq_nonneg (R n)]
  · have hp : 0 < R n ^ 2 := sq_pos_of_ne_zero (hnz hz)
    nlinarith
  · have hgain : 0 <
        ((((n + 1 : ℕ) : ℝ) ^ 3 * (2 * (n : ℝ) - 1) /
          ((n : ℝ) ^ 3 * (2 * (n : ℝ) + 1))) - 1) * z :=
      mul_pos (by linarith) hz
    linarith only [hgain, hwR']

#print axioms v_tail_strict

end D5.S1.Recurrence.Sun.VTail
