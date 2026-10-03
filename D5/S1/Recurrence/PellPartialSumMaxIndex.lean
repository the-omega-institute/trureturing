/- GID: D5/S1/Recurrence/PellPartialSumMaxIndex
   generality: I
   mirror-B: D5/B/S1/Recurrence/PellPartialSumMaxIndex
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pell partial sums have greatest dividing indices in four residue classes. -/

import D5.S1.Recurrence.PellCompanionGcd
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S1.Recurrence.PellPartialSumMaxIndex

open PellCompanionGcd

/-- The initial Pell sum `P₁ + ... + Pₙ`; the included zero term is `P₀=0`. -/
def partialSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), P i

/-- Byrapuram et al., Conjecture 18: greatest positive dividing indices in all four classes. -/
theorem result :
    (∀ k : ℕ, IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k + 1)} 1) ∧
    (∀ k : ℕ, IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k + 2)} 1) ∧
    (∀ k : ℕ, 1 ≤ k →
      IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k - 1)} (2 * k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum (4 * k)} (2 * k + 1)) := by
  have add (a b : ℕ) :
      P (a + b) = P a * Q b + Q a * P b ∧
      Q (a + b) = Q a * Q b + 2 * P a * P b := by
    induction b with
    | zero => simp [P, Q]
    | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        (pell_companion_step (a + b)).1, (pell_companion_step (a + b)).2,
        ih.1, ih.2, (pell_companion_step b).1, (pell_companion_step b).2]
      constructor <;> ring
  have qpos (n : ℕ) : 0 < Q n := (companion_odd n).pos
  have strict : StrictMono P := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [(pell_companion_step n).1]
    exact Nat.lt_add_of_pos_right (qpos n)
  have pos (n : ℕ) (hn : 0 < n) : 0 < P n := by
    simpa [P] using strict hn
  have pleq (n : ℕ) : P n ≤ Q n := by
    cases n with
    | zero => simp [P, Q]
    | succ n =>
      rw [(pell_companion_step n).1, (pell_companion_step n).2]
      omega
  have pltq (n : ℕ) (hn : 2 ≤ n) : P n < Q n := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [(pell_companion_step t).1, (pell_companion_step t).2]
    have := pos t (by omega)
    omega
  have parity (n : ℕ) : P n % 2 = n % 2 := by
    induction n with
    | zero => simp [P]
    | succ n ih =>
      rw [(pell_companion_step n).1, Nat.add_mod, ih]
      obtain ⟨t, ht⟩ := companion_odd n
      omega
  have norm (n : ℕ) :
      if n % 2 = 0 then Q n ^ 2 = 2 * P n ^ 2 + 1
      else 2 * P n ^ 2 = Q n ^ 2 + 1 := by
    induction n with
    | zero => simp [P, Q]
    | succ n ih =>
      rw [(pell_companion_step n).1, (pell_companion_step n).2]
      have hmod := Nat.mod_lt n (by omega : 0 < 2)
      split_ifs at ih ⊢ <;> (try omega) <;> nlinarith
  have sum_succ (n : ℕ) : partialSum (n + 1) = partialSum n + P (n + 1) := by
    exact Finset.sum_range_succ P (n + 1)
  have sum_closed (n : ℕ) : 2 * partialSum n + 1 = P (n + 1) + P n := by
    induction n with
    | zero => simp [partialSum, P]
    | succ n ih =>
      rw [sum_succ]
      change 2 * (partialSum n + P (n + 1)) + 1 = P (n + 2) + P (n + 1)
      rw [P]
      omega
  have double (n : ℕ) : P (2 * n) = 2 * P n * Q n ∧
      Q (2 * n) = Q n ^ 2 + 2 * P n ^ 2 := by
    rw [show 2 * n = n + n by omega, (add n n).1, (add n n).2]
    constructor <;> ring
  have sums_even (r : ℕ) :
      if r % 2 = 0 then partialSum (2 * r) = 2 * P r * P (r + 1)
      else partialSum (2 * r) = Q r * Q (r + 1) := by
    have h := sum_closed (2 * r)
    rw [(pell_companion_step (2 * r)).1, (double r).1, (double r).2] at h
    rw [(pell_companion_step r).1, (pell_companion_step r).2]
    have hn := norm r
    split_ifs at hn ⊢ <;> nlinarith
  have sums_odd (r : ℕ) (hr : 1 ≤ r) :
      if r % 2 = 0 then partialSum (2 * r - 1) = 2 * P r ^ 2
      else partialSum (2 * r - 1) = Q r ^ 2 := by
    have h := sum_closed (2 * r - 1)
    have hs := pell_companion_step (2 * r)
    have hp : P (2 * r + 1) = 2 * P (2 * r) + P (2 * r - 1) := by
      have he : 2 * r + 1 = (2 * r - 1) + 2 := by omega
      calc
        P (2 * r + 1) = P ((2 * r - 1) + 2) := congrArg P he
        _ = 2 * P ((2 * r - 1) + 1) + P (2 * r - 1) := rfl
        _ = 2 * P (2 * r) + P (2 * r - 1) := by
          rw [show 2 * r - 1 + 1 = 2 * r by omega]
    have he : 2 * r - 1 + 1 = 2 * r := by omega
    rw [he] at h
    have hn := norm r
    have hd := (double r).2
    split_ifs at hn ⊢ <;> nlinarith
  have gcd_shift (a b : ℕ) : Nat.gcd (P a) (P (a + b)) = Nat.gcd (P a) (P b) := by
    rw [(add a b).1, Nat.gcd_mul_left_add_right]
    exact (pell_companion_coprime a).symm.gcd_mul_left_cancel_right (P b)
  have gcd_period (a b t : ℕ) :
      Nat.gcd (P a) (P (b + t * a)) = Nat.gcd (P a) (P b) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show b + (t + 1) * a = a + (b + t * a) by ring, gcd_shift, ih]
  have gcd_pell (a b : ℕ) : Nat.gcd (P a) (P b) = P (Nat.gcd a b) := by
    induction a, b using Nat.gcd.induction with
    | H0 b => simp [P]
    | H1 a b ha ih =>
      calc
        Nat.gcd (P a) (P b) = Nat.gcd (P a) (P (b % a + b / a * a)) := by
          rw [Nat.mod_add_div']
        _ = Nat.gcd (P a) (P (b % a)) := gcd_period a (b % a) (b / a)
        _ = Nat.gcd (P (b % a)) (P a) := Nat.gcd_comm _ _
        _ = P (Nat.gcd (b % a) a) := ih
        _ = P (Nat.gcd a b) := by rw [← Nat.gcd_rec]
  have pell_dvd (a b : ℕ) (h : a ∣ b) : P a ∣ P b := by
    have he := gcd_pell b a
    rw [Nat.gcd_eq_right h] at he
    exact he ▸ Nat.gcd_dvd_left (P b) (P a)
  have odd_coprime (m j : ℕ) (hm : Odd m) : Nat.Coprime (P m) (Q j) := by
    let g := Nat.gcd (P m) (Q j)
    have hgq : g ∣ Q j := Nat.gcd_dvd_right _ _
    have hgp : g ∣ P m := Nat.gcd_dvd_left _ _
    have hgdouble : g ∣ P (2 * j) := by
      rw [(double j).1]
      exact hgq.trans (Nat.dvd_mul_left _ _)
    have hgg : g ∣ P (Nat.gcd m j) := by
      have h := Nat.dvd_gcd hgp hgdouble
      rw [gcd_pell, hm.coprime_two_left.gcd_mul_left_cancel_right j] at h
      exact h
    have hgj : g ∣ P j :=
      hgg.trans (pell_dvd (Nat.gcd m j) j (Nat.gcd_dvd_right m j))
    change g = 1
    apply Nat.dvd_one.mp
    simpa only [(pell_companion_coprime j).gcd_eq_one] using Nat.dvd_gcd hgj hgq
  have odd_bound (a b m : ℕ) (hm : 1 ≤ m) (hd : P m ∣ Q a * Q b) : m ≤ 1 := by
    have hodd : Odd (Q a * Q b) := (companion_odd a).mul (companion_odd b)
    have hpm : Odd (P m) := hodd.of_dvd_nat hd
    have hmo : Odd m := by
      rw [Nat.odd_iff]
      rw [← parity]
      exact Nat.odd_iff.mp hpm
    have hc : Nat.Coprime (P m) (Q a * Q b) :=
      (odd_coprime m a hmo).mul_right (odd_coprime m b hmo)
    have hpone : P m = 1 := Nat.eq_one_of_dvd_coprimes hc dvd_rfl hd
    apply strict.le_iff_le.mp
    simpa only [P] using (le_of_eq hpone : P m ≤ 1)
  have compress (a b c : ℕ) (hd : a ∣ 2 * b * c) :
      a ∣ 2 * Nat.gcd a b * Nat.gcd a c := by
    have h : a ∣ Nat.gcd a 2 * Nat.gcd a (b * c) :=
      Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr (by simpa only [mul_assoc] using hd)
    have ht := Nat.mul_dvd_mul (Nat.gcd_dvd_right a 2)
      (Nat.gcd_mul_right_dvd_mul_gcd a b c)
    simpa only [mul_assoc] using h.trans ht
  have half (m d : ℕ) (hmd : d ∣ m) (hd : d < m) : 2 * d ≤ m := by
    by_contra h
    have he := Nat.eq_of_dvd_of_lt_two_mul (by omega : m ≠ 0) hmd (by omega)
    omega
  have product_le (d e : ℕ) : 2 * P d * P e ≤ P (d + e) := by
    rw [(add d e).1]
    have h1 := Nat.mul_le_mul_left (P d) (pleq e)
    have h2 := Nat.mul_le_mul_right (P e) (pleq d)
    nlinarith
  have square_bound (r m : ℕ) (hr : 2 ≤ r) (hd : P m ∣ 2 * P r ^ 2) : m ≤ r := by
    by_contra h
    have hmr : r < m := by omega
    let d := Nat.gcd m r
    have hdp : 0 < d := Nat.gcd_pos_of_pos_left r (by omega)
    have hdr : d ≤ r := Nat.gcd_le_right m (by omega)
    have hdm : d < m := by omega
    have hhalf : 2 * d ≤ m := half m d (Nat.gcd_dvd_left m r) hdm
    have hc : P m ∣ 2 * P d ^ 2 := by
      have h := compress (P m) (P r) (P r) (by simpa only [pow_two, mul_assoc] using hd)
      simpa only [gcd_pell, pow_two, mul_assoc] using h
    have hsz : 2 * P d ^ 2 < P m := by
      by_cases hlt : 2 * d < m
      · have hle := product_le d d
        have hg := strict hlt
        rw [show d + d = 2 * d by omega] at hle
        nlinarith
      · have he : m = 2 * d := by omega
        have hd2 : 2 ≤ d := by omega
        have hp := pos d hdp
        have hq := pltq d hd2
        rw [he, (double d).1]
        nlinarith
    have hpos : 0 < 2 * P d ^ 2 := by
      have := pos d hdp
      positivity
    have hle := Nat.le_of_dvd hpos hc
    omega
  have consecutive_bound (r m : ℕ) (hr : 1 ≤ r)
      (hd : P m ∣ 2 * P r * P (r + 1)) : m ≤ r + 1 := by
    by_contra h
    have hmr : r + 1 < m := by omega
    let d := Nat.gcd m r
    let e := Nat.gcd m (r + 1)
    have hdp : 0 < d := Nat.gcd_pos_of_pos_left r (by omega)
    have hep : 0 < e := Nat.gcd_pos_of_pos_left (r + 1) (by omega)
    have hdr : d ≤ r := Nat.gcd_le_right m (by omega)
    have her : e ≤ r + 1 := Nat.gcd_le_right m (by omega)
    have hdhalf := half m d (Nat.gcd_dvd_left m r) (by omega)
    have hehalf := half m e (Nat.gcd_dvd_left m (r + 1)) (by omega)
    have hsum : d + e < m := by
      have hcop : Nat.Coprime d e :=
        ((Nat.coprime_self_add_right).mpr (Nat.coprime_one_right r)).gcd_both m m
      by_contra hn
      have heq : d = e := by omega
      have hone : d = 1 := by simpa only [heq, Nat.gcd_self] using hcop.gcd_eq_one
      omega
    have hc : P m ∣ 2 * P d * P e := by
      simpa only [gcd_pell] using compress (P m) (P r) (P (r + 1)) hd
    have hsz := lt_of_le_of_lt (product_le d e) (strict hsum)
    have hpos : 0 < 2 * P d * P e := by
      have := pos d hdp
      have := pos e hep
      positivity
    have hle := Nat.le_of_dvd hpos hc
    omega
  have odd_greatest (a b n : ℕ) (he : partialSum n = Q a * Q b) :
      IsGreatest {j : ℕ | 1 ≤ j ∧ P j ∣ partialSum n} 1 := by
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · simp only [P, one_dvd]
    · intro m hm
      exact odd_bound a b m hm.1 (he ▸ hm.2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    apply odd_greatest (2 * k + 1) (2 * k + 1) (4 * k + 1)
    have h := sums_odd (2 * k + 1) (by omega)
    simpa only [show (2 * k + 1) % 2 ≠ 0 by omega, if_false, pow_two,
      show 2 * (2 * k + 1) - 1 = 4 * k + 1 by omega] using h
  · intro k
    apply odd_greatest (2 * k + 1) (2 * k + 2) (4 * k + 2)
    have h := sums_even (2 * k + 1)
    simpa only [show (2 * k + 1) % 2 ≠ 0 by omega, if_false,
      show 2 * (2 * k + 1) = 4 * k + 2 by omega,
      show 2 * k + 1 + 1 = 2 * k + 2 by omega] using h
  · intro k hk
    have he : partialSum (4 * k - 1) = 2 * P (2 * k) ^ 2 := by
      have h := sums_odd (2 * k) (by omega)
      simpa only [show (2 * k) % 2 = 0 by omega, if_true,
        show 2 * (2 * k) - 1 = 4 * k - 1 by omega] using h
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · rw [he, pow_two]
      exact ⟨2 * P (2 * k), by ring⟩
    · intro m hm
      exact square_bound (2 * k) m (by omega) (he ▸ hm.2)
  · intro k hk
    have he : partialSum (4 * k) = 2 * P (2 * k) * P (2 * k + 1) := by
      have h := sums_even (2 * k)
      simpa only [show (2 * k) % 2 = 0 by omega, if_true,
        show 2 * (2 * k) = 4 * k by omega] using h
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · rw [he]
      exact Nat.dvd_mul_left _ _
    · intro m hm
      exact consecutive_bound (2 * k) m (by omega) (he ▸ hm.2)

end D5.S1.Recurrence.PellPartialSumMaxIndex
