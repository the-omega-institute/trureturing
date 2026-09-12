/- GID: D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Data.Nat.Choose.Multinomial, Mathlib.Data.Nat.Factorization.PrimePow, Mathlib.NumberTheory.Padics.PadicVal.Basic, Mathlib.Tactic.Linarith]
   utility: none
   digest: Prime-power exactness for factorial-square divisibility via prime valuations and base-p digits. -/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith

open scoped Nat

/-!
# Exact factorial-square divisibility

For every natural `n >= 2`, the largest exponent of `n!` dividing `(n^2)!`
is `n + 1` exactly when `n` is a prime power.  The proof compares prime
factorizations through Legendre's digit-sum formula.  Its central estimate is
the submultiplicativity of the base-`p` digit sum, proved locally from the
factorial divisibility behind digit-sum subadditivity.
-/

namespace D5.S1.Recurrence.Invariants.FactorialSquareDivisibilityPrimePower

/-- OEIS A096127/A096126 (Murthy, 2004): exact factorial-square divisibility
characterizes prime powers. -/
theorem factorial_square_exact_divisibility_iff_prime_power :
    ∀ n : ℕ, 2 ≤ n →
      ((((n !) ^ (n + 1) ∣ (n ^ 2) !) ∧
        ¬ (n !) ^ (n + 2) ∣ (n ^ 2) !) ↔ IsPrimePow n) := by
  intro n hn
  have digitSum_mul_le (p : ℕ) (hp : p.Prime) (a b : ℕ) :
      (p.digits (a * b)).sum ≤ (p.digits a).sum * (p.digits b).sum := by
    have digitSum_add_le (x y : ℕ) :
        (p.digits (x + y)).sum ≤ (p.digits x).sum + (p.digits y).sum := by
      have hfac :
          (x !).factorization p + (y !).factorization p ≤
            ((x + y) !).factorization p := by
        have h := Nat.factorization_le_factorization_of_dvd_right
          (a := p) (Nat.factorial_mul_factorial_dvd_factorial_add x y)
          (mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero y))
          (Nat.factorial_ne_zero (x + y))
        simpa only [Nat.factorization_mul (Nat.factorial_ne_zero x)
          (Nat.factorial_ne_zero y), Finsupp.add_apply] using h
      have hx := Nat.sub_one_mul_factorization_factorial (n := x) hp
      have hy := Nat.sub_one_mul_factorization_factorial (n := y) hp
      have hxy := Nat.sub_one_mul_factorization_factorial (n := x + y) hp
      have hsx := Nat.digit_sum_le p x
      have hsy := Nat.digit_sum_le p y
      have hsxy := Nat.digit_sum_le p (x + y)
      have hx' :
          (p - 1) * (x !).factorization p + (p.digits x).sum = x := by
        omega
      have hy' :
          (p - 1) * (y !).factorization p + (p.digits y).sum = y := by
        omega
      have hxy' :
          (p - 1) * ((x + y) !).factorization p + (p.digits (x + y)).sum = x + y := by
        omega
      have hfac' :
          (p - 1) * (x !).factorization p + (p - 1) * (y !).factorization p ≤
            (p - 1) * ((x + y) !).factorization p := by
        simpa only [Nat.mul_add] using Nat.mul_le_mul_left (p - 1) hfac
      omega
    have digitSum_base_mul (x : ℕ) :
        (p.digits (p * x)).sum = (p.digits x).sum := by
      by_cases hx : x = 0
      · simp [hx]
      · rw [Nat.digits_base_mul hp.one_lt (Nat.pos_of_ne_zero hx)]
        simp
    have digitSum_nsmul_le (k x : ℕ) :
        (p.digits (k * x)).sum ≤ k * (p.digits x).sum := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.succ_mul]
        calc
          (p.digits (k * x + x)).sum ≤
              (p.digits (k * x)).sum + (p.digits x).sum := digitSum_add_le _ _
          _ ≤ k * (p.digits x).sum + (p.digits x).sum :=
            Nat.add_le_add_right ih _
          _ = (k + 1) * (p.digits x).sum := by simp [Nat.add_mul]
    have digitSum_ofDigits_le : ∀ L : List ℕ,
        (p.digits (Nat.ofDigits p L)).sum ≤
          (L.map fun d => (p.digits d).sum).sum := by
      intro L
      induction L with
      | nil => simp
      | cons d L ih =>
        simp only [Nat.ofDigits_cons, List.map_cons, List.sum_cons]
        calc
          (p.digits (d + p * Nat.ofDigits p L)).sum ≤
              (p.digits d).sum + (p.digits (p * Nat.ofDigits p L)).sum :=
            digitSum_add_le _ _
          _ = (p.digits d).sum + (p.digits (Nat.ofDigits p L)).sum := by
            rw [digitSum_base_mul]
          _ ≤ (p.digits d).sum + (L.map fun e => (p.digits e).sum).sum :=
            Nat.add_le_add_left ih _
    calc
      (p.digits (a * b)).sum =
          (p.digits (Nat.ofDigits p ((p.digits a).map (b * ·)))).sum := by
        rw [← Nat.mul_ofDigits b, Nat.ofDigits_digits, Nat.mul_comm]
      _ ≤ (((p.digits a).map (b * ·)).map fun d => (p.digits d).sum).sum :=
        digitSum_ofDigits_le _
      _ ≤ ((p.digits a).map fun d => d * (p.digits b).sum).sum := by
        simp only [List.map_map]
        refine List.sum_le_sum fun d _ => ?_
        change (p.digits (b * d)).sum ≤ d * (p.digits b).sum
        simpa only [Nat.mul_comm d b] using digitSum_nsmul_le d b
      _ = (p.digits a).sum * (p.digits b).sum := by
        simpa using List.sum_map_mul_right (p.digits a) (fun d => d)
          (p.digits b).sum
  have digitSum_eq_one_isPrimePow (p : ℕ) (hp : p.Prime) (m : ℕ) (hm : 2 ≤ m)
      (hs : (p.digits m).sum = 1) : IsPrimePow m := by
    have ofDigits_eq_zero_of_sum_eq_zero : ∀ L : List ℕ,
        L.sum = 0 → Nat.ofDigits p L = 0 := by
      intro L hL
      induction L with
      | nil => rfl
      | cons d L ih =>
        simp only [List.sum_cons] at hL
        have hd : d = 0 := by omega
        have htail : L.sum = 0 := by omega
        simp [Nat.ofDigits_cons, hd, ih htail]
    have ofDigits_eq_pow_of_sum_eq_one : ∀ L : List ℕ,
        L.sum = 1 → ∃ k : ℕ, Nat.ofDigits p L = p ^ k := by
      intro L hL
      induction L with
      | nil => simp at hL
      | cons d L ih =>
        simp only [List.sum_cons] at hL
        by_cases hd : d = 0
        · subst d
          have htail : L.sum = 1 := by omega
          obtain ⟨k, hk⟩ := ih htail
          refine ⟨k + 1, ?_⟩
          rw [Nat.ofDigits_cons, zero_add, hk, pow_succ']
        · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
          have hd1 : d = 1 := by omega
          have htail : L.sum = 0 := by omega
          refine ⟨0, ?_⟩
          simp [Nat.ofDigits_cons, hd1, ofDigits_eq_zero_of_sum_eq_zero L htail]
    obtain ⟨k, hk⟩ := ofDigits_eq_pow_of_sum_eq_one (p.digits m) hs
    have hpow : p ^ k = m := hk.symm.trans (Nat.ofDigits_digits p m)
    refine (isPrimePow_nat_iff m).2 ⟨p, k, hp, ?_, hpow⟩
    by_contra hkpos
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkpos
    subst k
    simp at hpow
    omega
  have lower_dvd : (n !) ^ (n + 1) ∣ (n ^ 2) ! := by
    apply (Nat.factorization_prime_le_iff_dvd
      (pow_ne_zero _ (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero (n ^ 2))).mp
    intro p hp
    let s := (p.digits n).sum
    let t := (p.digits (n ^ 2)).sum
    let v := (n !).factorization p
    let w := ((n ^ 2) !).factorization p
    have hs : s ≤ n := Nat.digit_sum_le p n
    have ht0 : t ≤ n ^ 2 := Nat.digit_sum_le p (n ^ 2)
    have hn0 : n ≠ 0 := by omega
    have hdigits_ne : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn0
    have hspos : 0 < s := by
      exact List.sum_pos_iff_exists_pos_nat.mpr
        ⟨_, List.getLast_mem hdigits_ne,
          Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn0)⟩
    have hmul : t ≤ s * s := by
      simpa only [pow_two, s, t] using digitSum_mul_le p hp n n
    have hsquare : s * s + n ≤ (n + 1) * s := by
      have hsub1 : s - 1 + 1 = s := Nat.sub_add_cancel hspos
      have hsubn : n - s + s = n := Nat.sub_add_cancel hs
      nlinarith [Nat.zero_le ((s - 1) * (n - s))]
    have hbound : t + n ≤ (n + 1) * s := by omega
    have hv : (p - 1) * v + s = n := by
      dsimp only [v, s]
      rw [Nat.sub_one_mul_factorization_factorial hp, Nat.sub_add_cancel (Nat.digit_sum_le p n)]
    have hw : (p - 1) * w + t = n ^ 2 := by
      dsimp only [w, t]
      rw [Nat.sub_one_mul_factorization_factorial hp,
        Nat.sub_add_cancel (Nat.digit_sum_le p (n ^ 2))]
    have hp0 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hbalance :
        (p - 1) * ((n + 1) * v) + (n + 1) * s =
          (p - 1) * w + (t + n) := by
      calc
        (p - 1) * ((n + 1) * v) + (n + 1) * s =
            (n + 1) * ((p - 1) * v + s) := by ring
        _ = (n + 1) * n := by rw [hv]
        _ = n ^ 2 + n := by ring
        _ = ((p - 1) * w + t) + n := by rw [hw]
        _ = (p - 1) * w + (t + n) := by omega
    have hscaled_add :
        (p - 1) * ((n + 1) * v) + (n + 1) * s ≤
          (p - 1) * w + (n + 1) * s := by
      rw [hbalance]
      exact Nat.add_le_add_left hbound _
    have hscaled : (p - 1) * ((n + 1) * v) ≤ (p - 1) * w := by
      exact Nat.le_of_add_le_add_right hscaled_add
    have hvw : (n + 1) * v ≤ w := le_of_mul_le_mul_left hscaled hp0
    simpa [Nat.factorization_pow, v, w] using hvw
  have next_dvd_of_not_prime_power (hnpp : ¬ IsPrimePow n) :
      (n !) ^ (n + 2) ∣ (n ^ 2) ! := by
    apply (Nat.factorization_prime_le_iff_dvd
      (pow_ne_zero _ (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero (n ^ 2))).mp
    intro p hp
    let s := (p.digits n).sum
    let t := (p.digits (n ^ 2)).sum
    let v := (n !).factorization p
    let w := ((n ^ 2) !).factorization p
    have hs : s ≤ n := Nat.digit_sum_le p n
    have ht0 : t ≤ n ^ 2 := Nat.digit_sum_le p (n ^ 2)
    have hn0 : n ≠ 0 := by omega
    have hdigits_ne : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn0
    have hspos : 0 < s := by
      exact List.sum_pos_iff_exists_pos_nat.mpr
        ⟨_, List.getLast_mem hdigits_ne,
          Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn0)⟩
    have hsne : s ≠ 1 := by
      intro hs1
      exact hnpp (digitSum_eq_one_isPrimePow p hp n hn hs1)
    have hs2 : 2 ≤ s := by omega
    have hmul : t ≤ s * s := by
      simpa only [pow_two, s, t] using digitSum_mul_le p hp n n
    have hsquare : s * s + 2 * n ≤ (n + 2) * s := by
      have hsub2 : s - 2 + 2 = s := Nat.sub_add_cancel hs2
      have hsubn : n - s + s = n := Nat.sub_add_cancel hs
      nlinarith [Nat.zero_le ((s - 2) * (n - s))]
    have hbound : t + 2 * n ≤ (n + 2) * s := by omega
    have hv : (p - 1) * v + s = n := by
      dsimp only [v, s]
      rw [Nat.sub_one_mul_factorization_factorial hp, Nat.sub_add_cancel (Nat.digit_sum_le p n)]
    have hw : (p - 1) * w + t = n ^ 2 := by
      dsimp only [w, t]
      rw [Nat.sub_one_mul_factorization_factorial hp,
        Nat.sub_add_cancel (Nat.digit_sum_le p (n ^ 2))]
    have hp0 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hbalance :
        (p - 1) * ((n + 2) * v) + (n + 2) * s =
          (p - 1) * w + (t + 2 * n) := by
      calc
        (p - 1) * ((n + 2) * v) + (n + 2) * s =
            (n + 2) * ((p - 1) * v + s) := by ring
        _ = (n + 2) * n := by rw [hv]
        _ = n ^ 2 + 2 * n := by ring
        _ = ((p - 1) * w + t) + 2 * n := by rw [hw]
        _ = (p - 1) * w + (t + 2 * n) := by omega
    have hscaled_add :
        (p - 1) * ((n + 2) * v) + (n + 2) * s ≤
          (p - 1) * w + (n + 2) * s := by
      rw [hbalance]
      exact Nat.add_le_add_left hbound _
    have hscaled : (p - 1) * ((n + 2) * v) ≤ (p - 1) * w := by
      exact Nat.le_of_add_le_add_right hscaled_add
    have hvw : (n + 2) * v ≤ w := le_of_mul_le_mul_left hscaled hp0
    simpa [Nat.factorization_pow, v, w] using hvw
  constructor
  · rintro ⟨_, hnot⟩
    by_contra hnpp
    exact hnot (next_dvd_of_not_prime_power hnpp)
  · intro hnpp
    refine ⟨lower_dvd, ?_⟩
    rintro hnext
    obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff n).1 hnpp
    have digitSum_pow (e : ℕ) : (p.digits (p ^ e)).sum = 1 := by
      rw [show p ^ e = p ^ e * 1 by omega,
        Nat.digits_base_pow_mul hp.one_lt (by omega)]
      simp [Nat.digits_of_lt p 1 (by omega) hp.one_lt]
    have hsn : (p.digits n).sum = 1 := by rw [← hpow, digitSum_pow]
    have hsn2 : (p.digits (n ^ 2)).sum = 1 := by
      rw [← hpow, ← pow_mul, digitSum_pow]
    have hfac := (Nat.factorization_prime_le_iff_dvd
      (pow_ne_zero _ (Nat.factorial_ne_zero n)) (Nat.factorial_ne_zero (n ^ 2))).mpr hnext p hp
    have hfac' : (n + 2) * (n !).factorization p ≤ ((n ^ 2) !).factorization p := by
      simpa [Nat.factorization_pow] using hfac
    have hv0 :
        (p - 1) * (n !).factorization p + (p.digits n).sum = n := by
      rw [Nat.sub_one_mul_factorization_factorial hp,
        Nat.sub_add_cancel (Nat.digit_sum_le p n)]
    have hv : (p - 1) * (n !).factorization p + 1 = n := by
      simpa only [hsn] using hv0
    have hw0 :
        (p - 1) * ((n ^ 2) !).factorization p + (p.digits (n ^ 2)).sum = n ^ 2 := by
      rw [Nat.sub_one_mul_factorization_factorial hp,
        Nat.sub_add_cancel (Nat.digit_sum_le p (n ^ 2))]
    have hw : (p - 1) * ((n ^ 2) !).factorization p + 1 = n ^ 2 := by
      simpa only [hsn2] using hw0
    have hscaled := Nat.mul_le_mul_left (p - 1) hfac'
    have hleft :
        (p - 1) * ((n + 2) * (n !).factorization p) + (n + 2) =
          n * (n + 2) := by
      calc
        (p - 1) * ((n + 2) * (n !).factorization p) + (n + 2) =
            (n + 2) * ((p - 1) * (n !).factorization p + 1) := by ring
        _ = (n + 2) * n := by rw [hv]
        _ = n * (n + 2) := Nat.mul_comm _ _
    have hright :
        (p - 1) * ((n ^ 2) !).factorization p + (n + 2) =
          n ^ 2 + (n + 1) := by omega
    have hcontra : n * (n + 2) ≤ n ^ 2 + (n + 1) := by
      rw [← hleft, ← hright]
      exact Nat.add_le_add_right hscaled _
    nlinarith

#print axioms factorial_square_exact_divisibility_iff_prime_power

end D5.S1.Recurrence.Invariants.FactorialSquareDivisibilityPrimePower
