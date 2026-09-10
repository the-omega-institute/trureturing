/- GID: D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral exponential weights decimate modulo two to the binary Catalan series. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import Mathlib.RingTheory.PowerSeries.Derivative

open PowerSeries Finset

namespace D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity

/-- Integral normalization, with the unused value at zero set to zero. -/
noncomputable def d (n : ℕ) : ℤ :=
  if hn : 2 ≤ n then
    (n - 1 : ℕ) * d (n - 1) + ∑ j ∈ range n,
      if _hj : 2 ≤ j ∧ j < n then
        ((j : ℤ) ^ 2 - 1) * (n - j : ℕ) * d j * d (n - j) else 0
  else if n = 1 then 1 else 0
termination_by n
decreasing_by all_goals omega

/-- The coefficients of the normalized exponential equation, including a(0)=1. -/
noncomputable def a (n : ℕ) : ℤ := if n = 0 then 1 else (n : ℤ) * d n

private theorem d_zero : d 0 = 0 := by rw [d]; norm_num
private theorem d_one : d 1 = 1 := by rw [d]; norm_num
private theorem a_zero : a 0 = 1 := by simp [a]
private theorem a_one : a 1 = 1 := by simp [a, d_one]

theorem d_recurrence (n : ℕ) (hn : 2 ≤ n) :
    d n = (n - 1 : ℕ) * d (n - 1) +
      ∑ j ∈ Ico 2 n, ((j : ℤ) ^ 2 - 1) * (n - j : ℕ) * d j * d (n - j) := by
  rw [d, dif_pos hn]
  congr 1
  simp only [dite_eq_ite]
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range, mem_Ico]
  omega

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = (n : ℤ) * d n := by
  simp [a, show n ≠ 0 by omega]

/-- The integral series X L', where L is the exponent in the OEIS equation. -/
noncomputable def M : PowerSeries ℤ :=
  mk (fun n => if n = 0 then 0 else if n = 1 then 1 else ((n : ℤ) ^ 2 - 1) * d n)

private theorem coeff_M (n : ℕ) (hn : 2 ≤ n) :
    coeff n M = ((n : ℤ) ^ 2 - 1) * d n := by
  simp [M, show n ≠ 0 by omega, show n ≠ 1 by omega]

private theorem convolution (n : ℕ) (hn : 2 ≤ n) :
    coeff n (M * mk a) = ((n : ℤ) ^ 2 - 1) * d n +
      (n - 1 : ℕ) * d (n - 1) +
      ∑ j ∈ Ico 2 n, ((j : ℤ) ^ 2 - 1) * (n - j : ℕ) * d j * d (n - j) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i M * coeff j (mk a)) n, sum_range_succ]
  simp only [coeff_mk, Nat.sub_self, a_zero, mul_one]
  rw [← sum_range_add_sum_Ico _ hn]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero]
  have hz : coeff 0 M = 0 := by simp [M]
  have ho : coeff 1 M = 1 := by simp [M]
  rw [hz, ho, zero_mul, one_mul, zero_add, a_eq (n - 1) (by omega), coeff_M n hn]
  rw [add_comm _ (((n : ℤ) ^ 2 - 1) * d n), add_assoc]
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  obtain ⟨hj2, hjn⟩ := mem_Ico.mp hj
  rw [coeff_M j hj2, a_eq (n - j) (by omega)]
  ring

/-- Formal exponential reading: A(0)=1 and X A' = (X L') A. -/
theorem log_derivative_identity :
    coeff 0 (mk a) = 1 ∧ X * derivative ℤ (mk a) = M * mk a := by
  refine ⟨by simp [a_zero], ?_⟩
  ext n
  rcases n with _ | n
  · simp [M]
  by_cases hn : n + 1 = 1
  · have : n = 0 := by omega
    subst n
    rw [coeff_succ_X_mul, coeff_derivative, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i M * coeff j (mk a)) 1]
    simp [sum_range_succ, M, a_zero, a_one]
  · rw [convolution (n + 1) (by omega), coeff_succ_X_mul, coeff_derivative,
      coeff_mk, a_eq (n + 1) (by omega), add_assoc,
      ← d_recurrence (n + 1) (by omega)]
    push_cast
    ring

theorem coeff_M_rat (n : ℕ) (hn : 2 ≤ n) :
    coeff n (M.map (Int.castRingHom ℚ)) =
      ((n : ℚ) ^ 2 - 1) * (a n : ℚ) / n := by
  rw [coeff_map, coeff_M n hn, a_eq n (by omega)]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change ((((n : ℤ) ^ 2 - 1) * d n : ℤ) : ℚ) = _
  push_cast
  field_simp

private theorem rational_identity :
    X * derivative ℚ (mk (fun n => (a n : ℚ))) =
      M.map (Int.castRingHom ℚ) * mk (fun n => (a n : ℚ)) := by
  have ha : (mk a).map (Int.castRingHom ℚ) = mk (fun n => (a n : ℚ)) := by
    ext n
    simp
  have hd : (derivative ℤ (mk a)).map (Int.castRingHom ℚ) =
      derivative ℚ ((mk a).map (Int.castRingHom ℚ)) := by
    ext n
    simp [coeff_derivative]
  have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) log_derivative_identity.2
  simpa only [map_mul, map_X, hd, ha] using he

private theorem convolution_split (b : ℕ → ℚ) (m : PowerSeries ℚ)
    (hb : b 0 = 1) (hm : coeff 0 m = 0) (n : ℕ) (hn : 1 ≤ n) :
    coeff n (m * mk b) = coeff n m +
      ∑ j ∈ Ico 1 n, coeff j m * b (n - j) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i m * coeff j (mk b)) n, sum_range_succ]
  simp only [coeff_mk, Nat.sub_self, hb, mul_one]
  rw [← sum_range_add_sum_Ico _ hn]
  simp [hm, add_comm]

/-- The exact rational coefficient shape determines a unique solution. -/
theorem generating_unique (b : ℕ → ℚ) (m : PowerSeries ℚ)
    (hb0 : b 0 = 1) (hm0 : coeff 0 m = 0) (hm1 : coeff 1 m = 1)
    (hshape : ∀ n : ℕ, 2 ≤ n → coeff n m = ((n : ℚ) ^ 2 - 1) * b n / n)
    (heq : X * derivative ℚ (mk b) = m * mk b) :
    ∀ n : ℕ, b n = (a n : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [hb0, a_zero]
    have hn : 1 ≤ n := by omega
    have hprev : ∀ j < n, coeff j m = coeff j (M.map (Int.castRingHom ℚ)) := by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simp [hm0, M]
      by_cases hj1 : j = 1
      · subst j
        simp [hm1, M]
      rw [hshape j (by omega), coeff_M_rat j (by omega), ih j hj]
    have hs : (∑ j ∈ Ico 1 n, coeff j m * b (n - j)) =
        ∑ j ∈ Ico 1 n, coeff j (M.map (Int.castRingHom ℚ)) * (a (n - j) : ℚ) := by
      apply sum_congr rfl
      intro j hj
      obtain ⟨hj1, hjn⟩ := mem_Ico.mp hj
      rw [hprev j hjn, ih (n - j) (by omega)]
    have hx (f : PowerSeries ℚ) : coeff n (X * derivative ℚ f) =
        coeff n f * (n : ℚ) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      simp [coeff_succ_X_mul, coeff_derivative]
    have hleft := congrArg (coeff n) heq
    have hright := congrArg (coeff n) rational_identity
    rw [convolution_split b m hb0 hm0 n hn, hx, coeff_mk, hs] at hleft
    rw [convolution_split (fun n => (a n : ℚ)) _
      (by simp [a_zero]) (by simp [M]) n hn, hx, coeff_mk] at hright
    by_cases hn1 : n = 1
    · subst n
      simp [hm1, M, a_one] at hleft ⊢
      exact hleft
    rw [hshape n (by omega)] at hleft
    rw [coeff_M_rat n (by omega)] at hright
    have hdiff : (b n - (a n : ℚ)) * n =
        ((n : ℚ) ^ 2 - 1) * (b n - (a n : ℚ)) / n := by
      linear_combination hleft - hright
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    field_simp at hdiff
    nlinarith

private theorem reduced_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (d n : ZMod 2) = (n - 1 : ℕ) * (d (n - 1) : ZMod 2) +
      ∑ j ∈ range n, ((j : ZMod 2) ^ 2 - 1) * (n - j : ℕ) *
        (d j : ZMod 2) * (d (n - j) : ZMod 2) := by
  have hs : (∑ j ∈ range n,
      ((j : ℤ) ^ 2 - 1) * (n - j : ℕ) * d j * d (n - j)) =
      ∑ j ∈ Ico 2 n, ((j : ℤ) ^ 2 - 1) * (n - j : ℕ) * d j * d (n - j) := by
    rw [← sum_range_add_sum_Ico _ hn]
    simp [sum_range_succ, d_zero]
  have he := congrArg (Int.castRingHom (ZMod 2)) (d_recurrence n hn)
  rw [← hs] at he
  simpa using he

private theorem binary (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hv : x.val = 0 ∨ x.val = 1 := by have := ZMod.val_lt x; omega
  rcases hv with hv | hv
  · left
    have he := ZMod.natCast_zmod_val x
    simpa only [hv, Nat.cast_zero] using he.symm
  · right
    have he := ZMod.natCast_zmod_val x
    simpa only [hv, Nat.cast_one] using he.symm

private theorem even_pair (m : ℕ) (hm : 1 ≤ m) :
    (d (2 * m) : ZMod 2) = (d (2 * m - 1) : ZMod 2) := by
  rw [reduced_recurrence (2 * m) (by omega)]
  have hp : ((2 * m - 1 : ℕ) : ZMod 2) = 1 := by
    rw [Nat.cast_sub (by omega)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, show (2 : ZMod 2) = 0 by decide,
      zero_mul, Nat.cast_one, zero_sub]
    decide
  rw [hp, one_mul]
  have hs : (∑ j ∈ range (2 * m), ((j : ZMod 2) ^ 2 - 1) *
      (2 * m - j : ℕ) * (d j : ZMod 2) * (d (2 * m - j) : ZMod 2)) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [Nat.cast_sub (by have := mem_range.mp hj; omega)]
    rcases binary (j : ZMod 2) with h | h <;>
      simp [h, show (2 : ZMod 2) = 0 by decide]
  rw [hs, add_zero]

private theorem sum_pairs {R : Type*} [AddCommMonoid R] (f : ℕ → R) (m : ℕ) :
    ∑ j ∈ range (2 * m), f j = ∑ r ∈ range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    exact add_assoc _ _ _

private theorem odd_catalan (m : ℕ) :
    (d (2 * m + 1) : ZMod 2) =
      if m = 0 then 1 else ∑ r ∈ range m,
        (d (2 * r + 1) : ZMod 2) * (d (2 * (m - 1 - r) + 1) : ZMod 2) := by
  by_cases hm : m = 0
  · subst m
    simp [d_one]
  rw [if_neg hm, reduced_recurrence (2 * m + 1) (by omega)]
  simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat,
    show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  let f : ℕ → ZMod 2 := fun j => ((j : ZMod 2) ^ 2 - 1) *
    (2 * m + 1 - j : ℕ) * (d j : ZMod 2) * (d (2 * m + 1 - j) : ZMod 2)
  change ∑ j ∈ range (2 * m + 1), f j = _
  have hlast : f (2 * m + 1) = 0 := by simp [f]
  have hext : (∑ j ∈ range (2 * m + 1), f j) =
      ∑ j ∈ range (2 * (m + 1)), f j := by
    conv_rhs =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        sum_range_succ, hlast, add_zero]
  rw [hext, sum_pairs, sum_range_succ']
  have hstart : f 0 + f 1 = 0 := by simp [f, d_zero]
  rw [hstart, add_zero]
  apply sum_congr rfl
  intro r hr
  have hrm : r < m := mem_range.mp hr
  have heven : f (2 * (r + 1)) =
      (d (2 * r + 1) : ZMod 2) * (d (2 * (m - 1 - r) + 1) : ZMod 2) := by
    dsimp [f]
    rw [Nat.cast_sub (by omega)]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add, zero_pow (by decide : 2 ≠ 0),
      zero_sub, sub_zero, mul_one]
    rw [even_pair (r + 1) (by omega)]
    have hneg : (-1 : ZMod 2) = 1 := by decide
    rw [hneg, one_mul]
    rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega,
      show 2 * m + 1 - 2 * (r + 1) = 2 * (m - 1 - r) + 1 by omega]
  have hodd : f (2 * (r + 1) + 1) = 0 := by
    simp [f, show (2 : ZMod 2) = 0 by decide]
  rw [heven, hodd, add_zero]

private noncomputable def E : PowerSeries (ZMod 2) :=
  mk (fun m => (d (2 * m + 1) : ZMod 2))

private theorem E_equation : E = 1 + X * E ^ 2 := by
  ext n
  cases n with
  | zero => simp [E, d_one]
  | succ n =>
    rw [map_add, coeff_one, if_neg (by omega), zero_add, coeff_succ_X_mul,
      pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i E * coeff j E) n]
    simp only [E, coeff_mk]
    rw [odd_catalan (n + 1), if_neg (by omega)]
    simp only [Nat.add_sub_cancel]

private theorem quadratic_unique {F G : PowerSeries (ZMod 2)}
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0)
    (eF : F = X + F ^ 2) (eG : G = X + G ^ 2) : F = G := by
  have hu : IsUnit (1 - F - G) := by
    rw [isUnit_iff_constantCoeff]
    simp [hF, hG]
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  linear_combination eF - eG

theorem mod_two_catalan :
    X * mk (fun m => (d (2 * m + 1) : ZMod 2)) =
      Invariants.CatalanCompositionSquareParity.catalanSeries.map
        (Int.castRingHom (ZMod 2)) := by
  let hom := Int.castRingHom (ZMod 2)
  let K := Invariants.CatalanCompositionSquareParity.catalanSeries.map hom
  have hK : constantCoeff K = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp only [K, coeff_map, coeff_zero_eq_constantCoeff,
      Invariants.CatalanCompositionSquareParity.catalan_equation.1, map_zero]
  have eK : K = X + K ^ 2 := by
    simpa [K] using congrArg (PowerSeries.map hom)
      Invariants.CatalanCompositionSquareParity.catalan_equation.2.2
  change X * E = K
  apply quadratic_unique (by simp) hK _ eK
  linear_combination X * E_equation

private theorem odd_index_support (m : ℕ) :
    (d (2 * m + 1) : ZMod 2) = 1 ↔ ∃ k : ℕ, m + 1 = 2 ^ k := by
  have he := congrArg (coeff (m + 1)) mod_two_catalan
  simp only [coeff_succ_X_mul, coeff_mk] at he
  rw [he]
  exact Invariants.CatalanCompositionSquareParity.binary_catalan (m + 1)

/-- The first conjecture in OEIS A397242, including its constant coefficient. -/
theorem hanna_conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  by_cases hn0 : n = 0
  · subst n
    simp [a_zero]
    exact ⟨0, rfl⟩
  rw [← ZMod.intCast_eq_one_iff_odd, a_eq n (by omega)]
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    have hc : (((n : ℤ) * d n : ℤ) : ZMod 2) = 0 := by
      push_cast
      rw [he]
      simp [show (2 : ZMod 2) = 0 by decide]
    rw [hc]
    constructor
    · intro h
      exact (zero_ne_one h).elim
    · rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk; omega
      | succ k => rw [pow_succ] at hk; omega
  · let m := n / 2
    have he : n = 2 * m + 1 := by dsimp [m]; omega
    have hc : (((n : ℤ) * d n : ℤ) : ZMod 2) = (d (2 * m + 1) : ZMod 2) := by
      rw [he]
      push_cast
      simp [show (2 : ZMod 2) = 0 by decide]
    rw [hc, odd_index_support]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [pow_succ, ← hk]
      omega
    · rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        refine ⟨k, ?_⟩
        rw [pow_succ] at hk
        omega

#print axioms d_recurrence
#print axioms a_eq
#print axioms log_derivative_identity
#print axioms coeff_M_rat
#print axioms generating_unique
#print axioms mod_two_catalan
#print axioms hanna_conjecture

end D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity
