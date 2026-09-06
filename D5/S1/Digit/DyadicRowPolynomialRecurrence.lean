/- GID: D5/S1/Digit/DyadicRowPolynomialRecurrence
   generality: G
   mirror-B: D5/B/S1/Digit/DyadicRowPolynomialRecurrence
   mirror-E: none(waiver:symbolic-unbounded-identities)
   anchors: []
   utility: none
   digest: Dyadic row recurrence and Pascal accumulator identities for OEIS A373183. -/

import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.MaxPowDiv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.DyadicRowPolynomialRecurrence

open Polynomial

noncomputable def D (P : Polynomial Int) : Polynomial Int :=
  X * (P.comp (X + 1) - P)

theorem D_add (P Q : Polynomial Int) : D (P + Q) = D P + D Q := by
  simp only [D, add_comp]
  ring

theorem D_X : D X = X := by
  simp [D]

theorem D_X_mul (P : Polynomial Int) :
    D (X * P) = X * P + (X + 1) * D P := by
  simp only [D, mul_comp, X_comp]
  ring

noncomputable def R (n : Nat) : Polynomial Int :=
  if h : n = 0 then X
  else if n % 2 = 0 then D (R (n / 2)) else X * R (n / 2)
termination_by n
decreasing_by all_goals exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

theorem R_zero : R 0 = X := by rw [R]; simp

theorem R_odd (n : Nat) : R (2 * n + 1) = X * R n := by
  rw [R]
  simp [Nat.add_div]

/-- The even recurrence at positive indices. -/
theorem R_even (n : Nat) (hn : 0 < n) :
    R (2 * n) = X * ((R n).comp (X + 1) - R n) := by
  rw [R]
  simp [Nat.ne_of_gt hn, D]

private theorem R_even_D (n : Nat) : R (2 * n) = D (R n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.mul_zero, R_zero, D] using D_X.symm
  · simpa only [D] using R_even n (Nat.pos_of_ne_zero hn)

/-- The even-row formula proposed as OEIS A373183 Conjecture 1. -/
theorem conjecture1 (n : Nat) (hn : 0 < n) :
    R (2 * n) = R n + R (n - 2 ^ padicValNat 2 n) +
      R (2 * n - 2 ^ padicValNat 2 n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : n % 2 = 0
    · let k := n / 2
      have hk : 0 < k := by dsimp [k]; omega
      have hnk : n = 2 * k := by dsimp [k]; omega
      have hkl : k < n := by omega
      have hi := ih k hkl hk
      have hv : padicValNat 2 n = padicValNat 2 k + 1 := by
        rw [hnk, padicValNat_base_mul (by decide) (by omega)]
      have hs : n - 2 ^ padicValNat 2 n = 2 * (k - 2 ^ padicValNat 2 k) := by
        rw [hv, hnk, pow_succ, Nat.mul_comm (2 ^ _), Nat.mul_sub_left_distrib]
      have ht : 2 * n - 2 ^ padicValNat 2 n =
          2 * (2 * k - 2 ^ padicValNat 2 k) := by
        rw [hv, hnk, pow_succ, Nat.mul_comm (2 ^ _), Nat.mul_sub_left_distrib]
      rw [hs, ht, hnk]
      simpa only [R_even_D, D_add] using congrArg D hi
    · let k := n / 2
      have hnk : n = 2 * k + 1 := by dsimp [k]; omega
      have hv : padicValNat 2 n = 0 := by
        unfold padicValNat
        rw [Nat.maxPowDvdDiv_of_not_dvd (by omega : ¬ 2 ∣ n)]
      rw [hv, pow_zero, hnk]
      have hs : 2 * k + 1 - 1 = 2 * k := by omega
      have ht : 2 * (2 * k + 1) - 1 = 2 * (2 * k) + 1 := by omega
      rw [hs, ht, R_even_D, R_odd, D_X_mul, R_odd, R_even_D]
      ring

private theorem D_zero : D 0 = 0 := by simp [D]

private theorem D_C (a : Int) : D (C a) = 0 := by simp [D]

private theorem D_C_mul_X (a : Int) : D (C a * X) = C a * X := by
  simp only [D, mul_comp, C_comp, X_comp]
  ring

private theorem coeff_D_zero (P : Polynomial Int) : (D P).coeff 0 = 0 := by
  simp [D]

private theorem natDegree_D_le (P : Polynomial Int) : (D P).natDegree <= P.natDegree := by
  induction P using Polynomial.recOnHorner with
  | M0 => simp [D_zero]
  | MC P a hp ha ih =>
    rw [D_add, D_C, add_zero, natDegree_add_C]
    exact ih
  | MX P hp ih =>
    rw [natDegree_mul_X hp, mul_comm P X, D_X_mul]
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_X_mul hp).le
    · calc
        ((X + 1) * D P).natDegree <= (X + 1 : Polynomial Int).natDegree +
            (D P).natDegree := natDegree_mul_le
        _ <= P.natDegree + 1 := by
          have hx : (X + 1 : Polynomial Int).natDegree = 1 := by
            simpa only [C_1] using (natDegree_X_add_C (1 : Int))
          rw [hx]
          omega

def wt (n : Nat) : Nat := (Nat.digits 2 n).sum

private theorem wt_zero : wt 0 = 0 := by simp [wt]

private theorem wt_even (n : Nat) : wt (2 * n) = wt n := by
  by_cases hn : n = 0
  · simp [hn]
  · unfold wt
    rw [Nat.digits_base_mul (by decide) (Nat.pos_of_ne_zero hn)]
    simp

private theorem wt_odd (n : Nat) : wt (2 * n + 1) = wt n + 1 := by
  unfold wt
  rw [Nat.add_comm (2 * n), Nat.digits_add 2 (by decide) 1 n (by decide) (by simp)]
  simp [Nat.add_comm]

private theorem R_coeff_zero_all (n : Nat) : (R n).coeff 0 = 0 := by
  by_cases hn : n = 0
  · simp [hn, R_zero]
  · rw [R, dif_neg hn]
    split_ifs <;> simp [coeff_D_zero]

theorem R_coeff_zero (k : Nat) : (R (2 * k)).coeff 0 = 0 := by
  exact R_coeff_zero_all _

private theorem R_degree_all (n : Nat) : (R n).natDegree <= wt n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn, R_zero, wt_zero]
    · have hi := ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      by_cases he : n % 2 = 0
      · have h : n = 2 * (n / 2) := by omega
        conv_lhs => rw [h, R_even_D]
        have hw : wt n = wt (n / 2) := by conv_lhs => rw [h, wt_even]
        rw [hw]
        exact (natDegree_D_le _).trans hi
      · have h : n = 2 * (n / 2) + 1 := by omega
        conv_lhs => rw [h, R_odd]
        have hw : wt n = wt (n / 2) + 1 := by conv_lhs => rw [h, wt_odd]
        rw [hw]
        exact natDegree_mul_le.trans
          (by simpa [natDegree_X, Nat.add_comm] using Nat.add_le_add_right hi 1)

theorem R_degree (k : Nat) : (R (2 * k)).natDegree <= wt k + 1 := by
  simpa only [wt_even] using R_degree_all (2 * k)

private theorem R_binary_tail (m k : Nat) :
    R (2 ^ m * (2 * k + 1) - 1) = X ^ m * R (2 * k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : 0 < 2 ^ m * (2 * k + 1) := Nat.mul_pos (by positivity) (by omega)
    have ht : 2 ^ (m + 1) * (2 * k + 1) - 1 =
        2 * (2 ^ m * (2 * k + 1) - 1) + 1 := by
      rw [pow_succ, Nat.mul_right_comm (2 ^ m) 2]
      omega
    rw [ht, R_odd, ih, pow_succ]
    ring

theorem R_factorization (m k : Nat) :
    R (2 ^ (m + 1) * (2 * k + 1) - 2) = D (X ^ m * R (2 * k)) := by
  have ht : 2 ^ (m + 1) * (2 * k + 1) - 2 =
      2 * (2 ^ m * (2 * k + 1) - 1) := by
    rw [pow_succ, Nat.mul_right_comm (2 ^ m) 2, Nat.mul_comm _ 2,
      Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [ht, R_even_D, R_binary_tail]

private noncomputable def H (P : Polynomial Int) (d : Nat) : Nat -> Polynomial Int
  | 0 => 0
  | r + 1 => X * H P d r + C (if r < d then P.coeff (d - r) else 0) * X

private theorem H_zero_coeff (P : Polynomial Int) (d r : Nat) : (H P d r).coeff 0 = 0 := by
  cases r <;> simp only [H, coeff_zero, coeff_add, coeff_X_mul_zero, coeff_mul_X_zero, add_zero]

private theorem H_degree (P : Polynomial Int) (d r : Nat) : (H P d r).natDegree <= r := by
  induction r with
  | zero => simp [H]
  | succ r ih =>
    rw [H]
    apply natDegree_add_le_of_degree_le
    · exact natDegree_mul_le.trans
        (by simpa [natDegree_X, Nat.add_comm] using Nat.add_le_add_right ih 1)
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X]; omega)

private theorem H_coeff (P : Polynomial Int) (d r q : Nat) :
    (H P d r).coeff q =
      if 0 < q ∧ q <= r ∧ r < d + q then P.coeff (d + q - r) else 0 := by
  induction r generalizing q with
  | zero => rw [H, coeff_zero, if_neg (by omega)]
  | succ r ih =>
    cases q with
    | zero => simp [H_zero_coeff]
    | succ q =>
      rw [H]
      simp only [coeff_add, coeff_X_mul, coeff_mul_X, ih, coeff_C]
      by_cases hq : q = 0
      · subst q
        simp only [Nat.lt_irrefl, false_and, ite_false, true_and, add_zero, zero_add,
          Nat.zero_lt_succ, Nat.succ_le_succ_iff, Nat.zero_le, ite_true]
        have he : d + 1 - (r + 1) = d - r := by omega
        simp only [he]
        split_ifs <;> omega
      · have hp : 0 < q := by omega
        simp only [hq, ite_false, add_zero, hp, true_and, Nat.zero_lt_succ,
          Nat.succ_le_succ_iff]
        have he : d + (q + 1) - (r + 1) = d + q - r := by omega
        have hb : r + 1 < d + (q + 1) ↔ r < d + q := by omega
        simp only [he, hb]

private theorem H_at_degree (P : Polynomial Int) (d : Nat)
    (h0 : P.coeff 0 = 0) (hd : P.natDegree <= d) : H P d d = P := by
  ext q
  rw [H_coeff]
  by_cases hq : q = 0
  · simp [hq, h0]
  · by_cases hqd : q <= d
    · have hp : 0 < q := by omega
      simp [hp, hqd]
    · rw [if_neg (by omega)]
      exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

private theorem H_after_degree (P : Polynomial Int) (d m : Nat)
    (h0 : P.coeff 0 = 0) (hd : P.natDegree <= d) :
    H P d (d + m) = X ^ m * P := by
  induction m with
  | zero => simpa using H_at_degree P d h0 hd
  | succ m ih =>
    rw [show d + (m + 1) = (d + m) + 1 by omega, H, if_neg (by omega), C_0,
      zero_mul, add_zero, ih, pow_succ]
    ring

private theorem D_H_step (P : Polynomial Int) (d r : Nat) :
    D (H P d (r + 1)) = (X + 1) * D (H P d r) + H P d (r + 1) := by
  rw [H, D_add, D_X_mul, D_C_mul_X]
  ring

noncomputable def T (n q : Nat) : Int := (R n).coeff q

noncomputable def e (r k q : Nat) : Int :=
  match r with
  | 0 => 0
  | 1 => if q = 1 then T (2 * k) (wt k + 1) else 0
  | r + 2 => if 0 < q ∧ q <= r + 2 then
      e (r + 1) k q + e (r + 1) k (q - 1) +
        (if r + 2 <= wt k + q then T (2 * k) (wt k + q + 1 - (r + 2)) else 0)
    else 0

/-- The independently defined accumulator vanishes outside its support. -/
theorem e_support (r k q : Nat) (hq : q = 0 ∨ r < q) : e r k q = 0 := by
  cases r with
  | zero => rfl
  | succ r =>
    cases r with
    | zero => rw [e, if_neg (by omega)]
    | succ r => rw [e, if_neg (by omega)]

/-- The initial accumulator coefficient. -/
theorem e_one (k : Nat) : e 1 k 1 = T (2 * k) (wt k + 1) := by
  simp [e]

/-- The Pascal-type recurrence on the support interval. -/
theorem e_recurrence (r k q : Nat) (hr : 2 ≤ r) (hq : 0 < q ∧ q ≤ r) :
    e r k q = e (r - 1) k q + e (r - 1) k (q - 1) +
      (if r ≤ wt k + q then T (2 * k) (wt k + q + 1 - r) else 0) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 2 + r = r + 2 by omega, e, if_pos (by omega)]
  simp

private theorem e_zero (r k : Nat) : e r k 0 = 0 := by
  exact e_support r k 0 (Or.inl rfl)

private theorem e_outside (r k q : Nat) (hq : r < q) : e r k q = 0 := by
  exact e_support r k q (Or.inr hq)

private theorem e_eq_coeff_D_H (r k q : Nat) :
    e r k q = (D (H (R (2 * k)) (wt k + 1) r)).coeff q := by
  induction r generalizing q with
  | zero => simp [e, H, D_zero]
  | succ r ih =>
    cases r with
    | zero =>
      have hbase : e 1 k q = if q = 1 then T (2 * k) (wt k + 1) else 0 := by
        by_cases hq : q = 1
        · simpa only [hq, ite_true] using e_one k
        · rw [if_neg hq]
          exact e_support 1 k q (by omega)
      simp only [H, Nat.zero_lt_succ, ite_true, Nat.sub_zero, mul_zero, zero_add,
        D_C_mul_X, hbase, T]
      cases q with
      | zero => simp only [Nat.zero_ne_one, ite_false, coeff_mul_X_zero]
      | succ q =>
        simp only [coeff_mul_X, coeff_C, Nat.add_eq_right]
    | succ r =>
      by_cases hq0 : q = 0
      · subst q
        rw [e_zero, coeff_D_zero]
      · by_cases hq : q <= r + 2
        · rw [e_recurrence _ _ _ (by omega) (by omega)]
          simp only [Nat.add_sub_cancel]
          rw [D_H_step, add_mul, one_mul]
          obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
          simp only [Nat.succ_eq_add_one] at *
          simp only [coeff_add, coeff_X_mul, Nat.add_sub_cancel, ih, H_coeff]
          have hb : r + 2 <= wt k + (q + 1) ↔ r + 1 + 1 < wt k + 1 + (q + 1) := by omega
          have he : wt k + (q + 1) + 1 - (r + 2) = wt k + 1 + (q + 1) - (r + 1 + 1) := by omega
          have hg : 0 < q + 1 ∧ q + 1 <= r + 1 + 1 := by omega
          simp only [hg.1, hg.2, true_and, hb, he, T]
          ring
        · rw [e_outside _ _ _ (by omega)]
          symm
          exact coeff_eq_zero_of_natDegree_lt ((natDegree_D_le _).trans (H_degree _ _ _)
            |>.trans_lt (by omega))

noncomputable def E (r k : Nat) : Polynomial Int :=
  ∑ q ∈ Finset.range (r + 1), monomial q (e r k q)

private theorem E_coeff (r k q : Nat) : (E r k).coeff q = e r k q := by
  simp only [E, finsetSum_coeff, coeff_monomial]
  by_cases hq : q < r + 1
  · simp [hq]
  · simp [hq, e_outside r k q (by omega)]

private theorem E_eq_D_H (r k : Nat) : E r k = D (H (R (2 * k)) (wt k + 1) r) := by
  ext q
  rw [E_coeff, e_eq_coeff_D_H]

theorem E_at_degree (k : Nat) : E (wt k + 1) k = D (R (2 * k)) := by
  rw [E_eq_D_H, H_at_degree _ _ (R_coeff_zero k) (R_degree k)]

theorem E_after_degree (m k : Nat) :
    E (wt k + 1 + m) k = D (X ^ m * R (2 * k)) := by
  rw [E_eq_D_H, H_after_degree _ _ _ (R_coeff_zero k) (R_degree k)]

/-- The coefficient identity proposed as OEIS A373183 Conjecture 9. -/
theorem conjecture9 (m k q : Nat) (_hq : 0 < q) :
    T (2 ^ (m + 1) * (2 * k + 1) - 2) q = e (m + wt k + 1) k q := by
  unfold T
  rw [R_factorization, ← E_after_degree, E_coeff]
  congr 1
  omega

-- These examples check source fidelity; they are not computational deposit content.
example : Nonempty (Polynomial Int) := ⟨X⟩
example : ∃ n : Nat, 0 < n := ⟨1, by decide⟩
example : ∃ m k q : Nat, m = 0 ∧ k = 0 ∧ 0 < q := ⟨0, 0, 1, rfl, rfl, by decide⟩
example : R 1 = X ^ 2 := by
  simpa [R_zero, pow_two] using R_odd 0
example : R 2 = X + 2 * X ^ 2 := by
  have h : R 1 = X ^ 2 := by simpa [R_zero, pow_two] using R_odd 0
  rw [show 2 = 2 * 1 by rfl, R_even 1 (by decide), h]
  simp only [pow_comp, X_comp]
  ring
example : e 1 0 1 = 1 := by
  simp [e_one, T, R_zero, wt]
example : e 2 0 3 = 0 := e_support 2 0 3 (Or.inr (by decide))
example : T (2 ^ (0 + 1) * (2 * 0 + 1) - 2) 1 = e (0 + wt 0 + 1) 0 1 :=
  conjecture9 0 0 1 (by decide)

end D5.S1.Digit.DyadicRowPolynomialRecurrence
