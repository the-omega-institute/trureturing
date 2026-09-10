/- GID: D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/ParametricExponentialSquareCongruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Odd parameters transport parity; endpoint separation gives residues modulo eight. -/

import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Exp

open PowerSeries Finset

namespace D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence

/-- Integer normalization for the exponential square-weight family; the zero slot is unused. -/
noncomputable def b (q : ℤ) (n : ℕ) : ℤ :=
  if hn : 2 ≤ n then
    q * (n - 1 : ℕ) * b q (n - 1) + ∑ j ∈ range n,
      if _hj : 2 ≤ j ∧ j < n then
        (q * (j : ℤ) ^ 2 - 1) * (n - j : ℕ) * b q j * b q (n - j) else 0
  else if n = 1 then 1 else 0
termination_by n
decreasing_by all_goals omega

/-- The coefficient at zero is one, and positive coefficients are n times the normalization. -/
noncomputable def a (q : ℤ) (n : ℕ) : ℤ := if n = 0 then 1 else (n : ℤ) * b q n

private theorem b_zero (q : ℤ) : b q 0 = 0 := by rw [b]; norm_num
private theorem b_one (q : ℤ) : b q 1 = 1 := by rw [b]; norm_num
private theorem a_zero (q : ℤ) : a q 0 = 1 := by simp [a]
private theorem a_one (q : ℤ) : a q 1 = 1 := by simp [a, b_one]

/-- The convolution is over precisely 2 <= j < n, with ring subtraction in its weight. -/
theorem b_recurrence (q : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    b q n = q * (n - 1 : ℕ) * b q (n - 1) +
      ∑ j ∈ Ico 2 n, (q * (j : ℤ) ^ 2 - 1) * (n - j : ℕ) * b q j * b q (n - j) := by
  rw [b, dif_pos hn]
  congr 1
  simp only [dite_eq_ite]
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range, mem_Ico]
  omega

theorem a_eq (q : ℤ) (n : ℕ) (hn : 1 ≤ n) : a q n = (n : ℤ) * b q n := by
  simp [a, show n ≠ 0 by omega]

/-- The integral series q X L', where L is the exponent in the OEIS equation. -/
noncomputable def M (q : ℤ) : PowerSeries ℤ :=
  mk (fun n => if n = 0 then 0 else if n = 1 then q else (q * (n : ℤ) ^ 2 - 1) * b q n)

private theorem coeff_M (q : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    coeff n (M q) = (q * (n : ℤ) ^ 2 - 1) * b q n := by
  simp [M, show n ≠ 0 by omega, show n ≠ 1 by omega]

private theorem convolution (q : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    coeff n (M q * mk (a q)) = (q * (n : ℤ) ^ 2 - 1) * b q n +
      q * (n - 1 : ℕ) * b q (n - 1) +
      ∑ j ∈ Ico 2 n, (q * (j : ℤ) ^ 2 - 1) * (n - j : ℕ) * b q j * b q (n - j) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (M q) * coeff j (mk (a q))) n, sum_range_succ]
  simp only [coeff_mk, Nat.sub_self, a_zero, mul_one]
  rw [← sum_range_add_sum_Ico _ hn]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero]
  have hz : coeff 0 (M q) = 0 := by simp [M]
  have ho : coeff 1 (M q) = q := by simp [M]
  rw [hz, ho, zero_mul, zero_add, a_eq q (n - 1) (by omega), coeff_M q n hn]
  rw [add_comm _ ((q * (n : ℤ) ^ 2 - 1) * b q n), add_assoc, ← mul_assoc]
  congr 1
  congr 1
  apply sum_congr rfl
  intro j hj
  obtain ⟨hj2, hjn⟩ := mem_Ico.mp hj
  rw [coeff_M q j hj2, a_eq q (n - j) (by omega)]
  ring

/-- Formal exponential reading: A(0)=1 and q X A' = (q X L') A. -/
theorem log_derivative_identity (q : ℤ) :
    coeff 0 (mk (a q)) = 1 ∧ C q * (X * derivative ℤ (mk (a q))) = M q * mk (a q) := by
  refine ⟨by simp [a_zero], ?_⟩
  ext n
  rcases n with _ | n
  · simp [M]
  by_cases hn : n + 1 = 1
  · have : n = 0 := by omega
    subst n
    rw [coeff_C_mul, coeff_succ_X_mul, coeff_derivative, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (M q) * coeff j (mk (a q))) 1]
    simp [sum_range_succ, M, a_zero, a_one]
  · rw [convolution q (n + 1) (by omega), coeff_C_mul, coeff_succ_X_mul, coeff_derivative,
      coeff_mk, a_eq q (n + 1) (by omega), add_assoc,
      ← b_recurrence q (n + 1) (by omega)]
    push_cast
    ring

theorem coeff_M_rat (q : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    coeff n ((M q).map (Int.castRingHom ℚ)) =
      ((q : ℚ) * (n : ℚ) ^ 2 - 1) * (a q n : ℚ) / n := by
  rw [coeff_map, coeff_M q n hn, a_eq q n (by omega)]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change (((q * (n : ℤ) ^ 2 - 1) * b q n : ℤ) : ℚ) = _
  push_cast
  field_simp

private theorem rational_identity (q : ℤ) :
    C (q : ℚ) * (X * derivative ℚ (mk (fun n => (a q n : ℚ)))) =
      (M q).map (Int.castRingHom ℚ) * mk (fun n => (a q n : ℚ)) := by
  have ha : (mk (a q)).map (Int.castRingHom ℚ) = mk (fun n => (a q n : ℚ)) := by
    ext n
    simp
  have hd : (derivative ℤ (mk (a q))).map (Int.castRingHom ℚ) =
      derivative ℚ ((mk (a q)).map (Int.castRingHom ℚ)) := by
    ext n
    simp [coeff_derivative]
  have he := congrArg (PowerSeries.map (Int.castRingHom ℚ)) (log_derivative_identity q).2
  simpa only [map_mul, map_C, map_X, hd, ha, Int.coe_castRingHom] using he

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
theorem generating_unique (q : ℤ) (hq : q ≠ 0) (b : ℕ → ℚ) (m : PowerSeries ℚ)
    (hb0 : b 0 = 1) (hm0 : coeff 0 m = 0) (hm1 : coeff 1 m = (q : ℚ))
    (hshape : ∀ n : ℕ, 2 ≤ n → coeff n m = ((q : ℚ) * (n : ℚ) ^ 2 - 1) * b n / n)
    (heq : C (q : ℚ) * (X * derivative ℚ (mk b)) = m * mk b) :
    ∀ n : ℕ, b n = (a q n : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [hb0, a_zero]
    have hn : 1 ≤ n := by omega
    have hprev : ∀ j < n, coeff j m = coeff j ((M q).map (Int.castRingHom ℚ)) := by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        simp [hm0, M]
      by_cases hj1 : j = 1
      · subst j
        simp [hm1, M]
      rw [hshape j (by omega), coeff_M_rat q j (by omega), ih j hj]
    have hs : (∑ j ∈ Ico 1 n, coeff j m * b (n - j)) =
        ∑ j ∈ Ico 1 n, coeff j ((M q).map (Int.castRingHom ℚ)) * (a q (n - j) : ℚ) := by
      apply sum_congr rfl
      intro j hj
      obtain ⟨hj1, hjn⟩ := mem_Ico.mp hj
      rw [hprev j hjn, ih (n - j) (by omega)]
    have hx (f : PowerSeries ℚ) : coeff n (X * derivative ℚ f) =
        coeff n f * (n : ℚ) := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      simp [coeff_succ_X_mul, coeff_derivative]
    have hleft := congrArg (coeff n) heq
    have hright := congrArg (coeff n) (rational_identity q)
    rw [convolution_split b m hb0 hm0 n hn, coeff_C_mul, hx, coeff_mk, hs] at hleft
    rw [convolution_split (fun n => (a q n : ℚ)) _
      (by simp [a_zero]) (by simp [M]) n hn, coeff_C_mul, hx, coeff_mk] at hright
    by_cases hn1 : n = 1
    · subst n
      have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq
      simpa [a_one] using (mul_left_cancel₀ hqq (by simpa [hm1] using hleft) : b 1 = 1)
    rw [hshape n (by omega)] at hleft
    rw [coeff_M_rat q n (by omega)] at hright
    have hdiff : (q : ℚ) * ((b n - (a q n : ℚ)) * n) =
        ((q : ℚ) * (n : ℚ) ^ 2 - 1) * (b n - (a q n : ℚ)) / n := by
      linear_combination hleft - hright
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    field_simp at hdiff
    nlinarith


/-- The exponent in the original OEIS equation; all divisions take place in Q. -/
noncomputable def exponent (q : ℤ) (f : ℕ → ℚ) : PowerSeries ℚ :=
  mk (fun n => if n = 0 then 0 else if n = 1 then 1 else
    ((q : ℚ) * (n : ℚ) ^ 2 - 1) * f n / ((q : ℚ) * (n : ℚ) ^ 2))

private theorem exponent_zero (q : ℤ) (f : ℕ → ℚ) :
    constantCoeff (exponent q f) = 0 := by simp [exponent]

private theorem exponent_shape (q : ℤ) (hq : q ≠ 0) (f : ℕ → ℚ) (n : ℕ)
    (hn : 2 ≤ n) :
    coeff n (C (q : ℚ) * (X * derivative ℚ (exponent q f))) =
      ((q : ℚ) * (n : ℚ) ^ 2 - 1) * f n / n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [coeff_C_mul, coeff_succ_X_mul, coeff_derivative]
  simp only [exponent, coeff_mk, if_neg (by omega : r + 1 ≠ 0),
    if_neg (by omega : r + 1 ≠ 1)]
  have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hrr : (r : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

private theorem exp_subst_zero (L : PowerSeries ℚ) (hL : constantCoeff L = 0) :
    constantCoeff ((exp ℚ).subst L) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_subst' (HasSubst.of_constantCoeff_zero' hL), finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [coeff_zero_eq_constantCoeff_apply, hL, zero_pow hn]

private theorem linear_ode_unique (F G H : PowerSeries ℚ)
    (h0 : coeff 0 F = coeff 0 G)
    (hF : derivative ℚ F = H * F) (hG : derivative ℚ G = H * G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      have hs : coeff n (H * F) = coeff n (H * G) := by
        rw [coeff_mul, coeff_mul]
        apply sum_congr rfl
        intro ij hij
        have hij' := Finset.mem_antidiagonal.mp hij
        rw [ih ij.2 (by omega)]
      have hf := congrArg (coeff n) hF
      have hg := congrArg (coeff n) hG
      rw [coeff_derivative] at hf hg
      have hnq : (n : ℚ) + 1 ≠ 0 := by positivity
      exact mul_right_cancel₀ hnq (hf.trans (hs.trans hg.symm))

/-- Exact equivalence with the source self-referential formal exponential equation. -/
theorem source_iff (q : ℤ) (hq : q ≠ 0) (f : ℕ → ℚ) :
    mk f = (exp ℚ).subst (exponent q f) ↔ ∀ n : ℕ, f n = (a q n : ℚ) := by
  let L := exponent q f
  let N := C (q : ℚ) * (X * derivative ℚ L)
  have hL0 : constantCoeff L = 0 := exponent_zero q f
  have hN0 : coeff 0 N = 0 := by simp [N]
  have hN1 : coeff 1 N = (q : ℚ) := by
    change coeff (0 + 1) (C (q : ℚ) * (X * derivative ℚ L)) = _
    rw [coeff_C_mul, coeff_succ_X_mul, coeff_derivative]
    simp [L, exponent]
  have hNshape : ∀ n : ℕ, 2 ≤ n →
      coeff n N = ((q : ℚ) * (n : ℚ) ^ 2 - 1) * f n / n :=
    exponent_shape q hq f
  have hE : derivative ℚ ((exp ℚ).subst L) = derivative ℚ L * (exp ℚ).subst L := by
    rw [derivative_subst (HasSubst.of_constantCoeff_zero' hL0), derivative_exp, mul_comm]
  constructor
  · intro heq
    have hf0 : f 0 = 1 := by
      have hz := exp_subst_zero L hL0
      rw [← heq, ← coeff_zero_eq_constantCoeff_apply, coeff_mk] at hz
      exact hz
    apply generating_unique q hq f N hf0 hN0 hN1 hNshape
    have hd : derivative ℚ (mk f) = derivative ℚ L * mk f := by
      simpa only [heq] using hE
    rw [hd]
    dsimp [N]
    ring
  · intro hf
    have heq : mk f = mk (fun n => (a q n : ℚ)) := by ext n; simp [hf]
    have hN : N = (M q).map (Int.castRingHom ℚ) := by
      ext n
      by_cases hn : 2 ≤ n
      · rw [hNshape n hn, hf n, coeff_M_rat q n hn]
      · interval_cases n <;> simp [hN0, hN1, M]
    have hscale := rational_identity q
    rw [← heq, ← hN] at hscale
    have hqq : (q : ℚ) ≠ 0 := by exact_mod_cast hq
    have hunit : C (q : ℚ) * (X : PowerSeries ℚ) ≠ 0 :=
      mul_ne_zero (by simpa only [map_zero] using C_injective.ne hqq) X_ne_zero
    have hF : derivative ℚ (mk f) = derivative ℚ L * mk f := by
      apply mul_left_cancel₀ hunit
      dsimp [N] at hscale
      linear_combination hscale
    apply linear_ode_unique (mk f) ((exp ℚ).subst L) (derivative ℚ L) _ hF hE
    rw [coeff_mk, hf 0, a_zero, Int.cast_one,
      coeff_zero_eq_constantCoeff_apply, exp_subst_zero L hL0]

/-- Odd parameters give the same normalized coefficients modulo two as the frozen q=1 series. -/
theorem normalized_mod_two (q : ℤ) (hq : Odd q) (n : ℕ) :
    (b q n : ZMod 2) = (ExponentialSquareWeightCatalanParity.d n : ZMod 2) := by
  have hq2 : (q : ZMod 2) = 1 := ZMod.intCast_eq_one_iff_odd.mpr hq
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2 ≤ n
    · rw [b_recurrence q n hn, ExponentialSquareWeightCatalanParity.d_recurrence n hn]
      push_cast
      rw [hq2, one_mul, ih (n - 1) (by omega)]
      congr 1
      apply sum_congr rfl
      intro j hj
      obtain ⟨hj2, hjn⟩ := mem_Ico.mp hj
      rw [one_mul, ih j hjn, ih (n - j) (by omega)]
    · interval_cases n <;> rw [b, ExponentialSquareWeightCatalanParity.d] <;> norm_num

/-- All odd integer parameters have the source's power-of-two parity support, including n=0. -/
theorem odd_parameter_parity (q : ℤ) (hq : Odd q) (n : ℕ) :
    Odd (a q n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  have he : (a q n : ZMod 2) = (ExponentialSquareWeightCatalanParity.a n : ZMod 2) := by
    by_cases hn : n = 0
    · subst n
      simp [a, ExponentialSquareWeightCatalanParity.a]
    · simp only [a, ExponentialSquareWeightCatalanParity.a, if_neg hn, Int.cast_mul,
        Int.cast_natCast, normalized_mod_two q hq n]
  rw [← ZMod.intCast_eq_one_iff_odd, he, ZMod.intCast_eq_one_iff_odd]
  exact ExponentialSquareWeightCatalanParity.hanna_conjecture n

private theorem four_sum (n : ℕ) :
    (∑ j ∈ range n, (4 : ZMod 8) * j) = 2 * (n : ZMod 8) * ((n : ZMod 8) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

private theorem interior_sum (n : ℕ) (hn : 3 ≤ n) :
    (∑ j ∈ Ico 2 (n - 1), (4 : ZMod 8) * (n - j : ℕ)) =
      2 * ((n : ZMod 8) - 2) * ((n : ZMod 8) - 1) - 4 := by
  rw [sum_Ico_reflect (fun j => (4 : ZMod 8) * j) 2 (by omega)]
  rw [show n + 1 - (n - 1) = 2 by omega, show n + 1 - 2 = n - 1 by omega]
  have hs := sum_range_add_sum_Ico (fun j => (4 : ZMod 8) * j) (show 2 ≤ n - 1 by omega)
  rw [four_sum, four_sum, Nat.cast_sub (by omega : 1 ≤ n)] at hs
  norm_num at hs
  linear_combination hs

private theorem residue_step (n : ℕ) (hn : 3 ≤ n) :
    (2 * (n : ZMod 8) * ((n : ZMod 8) - 1) - 1) *
        (if (n - 1) % 4 = 3 then 6 else 2) +
      (2 * ((n : ZMod 8) - 2) * ((n : ZMod 8) - 1) - 4) =
        if n % 4 = 3 then 6 else 2 := by
  have h8 := Nat.mod_lt n (by decide : 0 < 8)
  rw [← ZMod.natCast_mod n 8]
  interval_cases h : n % 8 <;>
    have hp : (n - 1) % 4 = (n % 8 + 3) % 4 := by omega
  all_goals have hc : n % 4 = (n % 8) % 4 := by omega
  all_goals simp [h] at hp hc
  all_goals norm_num [hp, hc] <;> decide

/-- The q=2 normalization is 6 at indices 3 modulo four, and 2 elsewhere after degree one. -/
theorem normalized_mod_eight (n : ℕ) (hn : 2 ≤ n) :
    (b 2 n : ZMod 8) = if n % 4 = 3 then 6 else 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n = 2
    · subst n
      rw [b_recurrence 2 2 (by omega)]
      norm_num [b_one]
    have hn3 : 3 ≤ n := by omega
    have hs (f : ℕ → ZMod 8) : ∑ j ∈ Ico 2 n, f j =
        (∑ j ∈ Ico 2 (n - 1), f j) + f (n - 1) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        sum_Ico_succ_top (by omega : 2 ≤ n - 1) f
    have he := congrArg (Int.castRingHom (ZMod 8)) (b_recurrence 2 n hn)
    simp only [Int.coe_castRingHom] at he
    push_cast at he
    rw [hs] at he
    have hi : (∑ j ∈ Ico 2 (n - 1), ((2 : ZMod 8) * (j : ZMod 8) ^ 2 - 1) *
        (n - j : ℕ) * (b 2 j : ZMod 8) * (b 2 (n - j) : ZMod 8)) =
        ∑ j ∈ Ico 2 (n - 1), (4 : ZMod 8) * (n - j : ℕ) := by
      apply sum_congr rfl
      intro j hj
      obtain ⟨hj2, hjn⟩ := mem_Ico.mp hj
      rw [ih j (by omega) hj2, ih (n - j) (by omega) (by omega)]
      split_ifs <;> ring_nf
      all_goals simp only [show (72 : ZMod 8) = 0 by decide,
        show (24 : ZMod 8) = 0 by decide, show (8 : ZMod 8) = 0 by decide,
        show (36 : ZMod 8) = 4 by decide, show (12 : ZMod 8) = 4 by decide,
        mul_zero, zero_sub, ← mul_neg, show (-4 : ZMod 8) = 4 by decide]
    rw [hi, interior_sum n hn3, show n - (n - 1) = 1 by omega, b_one,
      Int.cast_one, Nat.cast_one, mul_one, mul_one,
      ih (n - 1) (by omega) (by omega), Nat.cast_sub (by omega : 1 ≤ n)] at he
    have ht := residue_step n hn3
    rw [he]
    linear_combination ht

/-- OEIS A397346: from n=2 the residues are 4,2,0,2 with period four. -/
theorem residues_q2 (n : ℕ) (hn : 2 ≤ n) :
    a 2 n % 8 = if n % 4 = 2 then 4 else if n % 4 = 0 then 0 else 2 := by
  have he : (a 2 n : ZMod 8) =
      (if n % 4 = 2 then 4 else if n % 4 = 0 then 0 else 2 : ℤ) := by
    rw [a_eq 2 n (by omega), Int.cast_mul, Int.cast_natCast, normalized_mod_eight n hn]
    have h8 := Nat.mod_lt n (by decide : 0 < 8)
    rw [← ZMod.natCast_mod n 8]
    interval_cases h : n % 8 <;>
      have hc : n % 4 = (n % 8) % 4 := by omega
    all_goals simp [h] at hc
    all_goals norm_num [hc] <;> decide
  have hmod := (ZMod.intCast_eq_intCast_iff _ _ 8).mp he
  change a 2 n % 8 = _ % 8 at hmod
  split_ifs at hmod ⊢ <;> norm_num at hmod ⊢ <;> exact hmod

/-- The A397345 parity endpoint, specialized from the odd-parameter theorem. -/
theorem parity_q5 (n : ℕ) : Odd (a 5 n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k :=
  odd_parameter_parity 5 ⟨2, rfl⟩ n

/-- The A397348 parity endpoint, specialized from the odd-parameter theorem. -/
theorem parity_q3 (n : ℕ) : Odd (a 3 n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k :=
  odd_parameter_parity 3 ⟨1, rfl⟩ n

/-- The four dispatched conjectures, reusing the frozen q=1 sequence directly. -/
theorem family_conjectures :
    (∀ n : ℕ, Odd (a 5 n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k) ∧
    (∀ n : ℕ, Odd (a 3 n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k) ∧
    (∀ n : ℕ, Odd (ExponentialSquareWeightCatalanParity.a n) ↔
      ∃ k : ℕ, n + 1 = 2 ^ k) ∧
    (∀ n : ℕ, 2 ≤ n →
      a 2 n % 8 = if n % 4 = 2 then 4 else if n % 4 = 0 then 0 else 2) :=
  ⟨parity_q5, parity_q3,
    ExponentialSquareWeightCatalanParity.hanna_conjecture, residues_q2⟩

#print axioms family_conjectures
#print axioms source_iff
#print axioms log_derivative_identity
#print axioms generating_unique
#print axioms normalized_mod_eight
#print axioms residues_q2
#print axioms normalized_mod_two
#print axioms odd_parameter_parity

end D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence
