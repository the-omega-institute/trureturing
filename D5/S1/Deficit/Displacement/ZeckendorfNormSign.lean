/- GID: D5/S1/Deficit/Displacement/ZeckendorfNormSign
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   digest: The least occupied canonical Zeckendorf index determines the sign of the golden norm. -/

import D5.S1.Deficit.DoubleFaceLength
import D5.S1.Deficit.ZeckendorfDisplacementReading
import D5.S1.Scale.Fibonacci
import Mathlib

/- Provenance: Native proof over pinned mathlib. -/

/-! SEARCH RECEIPT (2026-08-18, pinned repository and pinned mathlib):
Repository searches across the deficit, digit, scale, and carrier families for
`deficit`, `dominance`, `tail`, `parity`, and the target coordinates found the
public ingredients `betaGolden_b`, `betaReal_sub_betaContraction`,
`embedding_mul_conj`, `wdigits_isCanonical`, and `decode_wdigits`. Existing
nonadjacent conjugate-tail arguments in `ZeckendorfDisplacementReading` and
`GoldenCubePeriodsSupport` are private, so their result cannot be imported.
Pinned mathlib supplies the exact Fibonacci residual
`Real.fib_succ_sub_goldenRatio_mul_fib`, parity laws for negative powers, list
`Pairwise`/`dropLast` lemmas, and ordered power comparison below one.

The proof reconstructs the missing public first coordinate of `betaGolden`,
then proves the required nonadjacent geometric-tail dominance locally. The
premises have separate roles: `hk` makes the canonical digit list nonempty,
`hmin` identifies its least digit, and `hv` makes the expanding embedding
strictly positive. No premise is added or discharged by fabricated data.
-/

open scoped BigOperators

namespace D5.S1.Deficit.Displacement.ZeckendorfNormSign

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Digit
open D5.S1.Scale
open D5.S1.Deficit.ZeckendorfDisplacementReading

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem betaDigits_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast
    ring

@[simp] private theorem betaDigits_single (i : ℕ) :
    betaDigits (Finsupp.single i 1) = phi ^ (i + 2) := by
  classical
  simp [betaDigits]

private theorem canonical_two_le {digits : List ℕ} (h : digits.IsZeckendorfRep) :
    ∀ k ∈ digits, 2 ≤ k := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at h
  intro k hk
  exact (List.pairwise_append.mp h).2.2 k hk 0 (by simp)

private theorem betaDigits_rawOfZeckendorf_a {digits : List ℕ}
    (hmin : ∀ k ∈ digits, 2 ≤ k) :
    (betaDigits (rawOfZeckendorf digits)).a =
      ((digits.map fun k => Nat.fib (k + 1)).sum : ℤ) -
        ((digits.map Nat.fib).sum : ℤ) := by
  induction digits with
  | nil => simp [rawOfZeckendorf, betaDigits]
  | cons k digits ih =>
      have hk : 2 ≤ k := hmin k (by simp)
      have htail : ∀ j ∈ digits, 2 ≤ j := by
        intro j hj
        exact hmin j (by simp [hj])
      have hraw : rawOfZeckendorf (k :: digits) =
          Finsupp.single (k - 2) 1 + rawOfZeckendorf digits := by
        rw [rawOfZeckendorf, List.map_cons]
        change Multiset.toFinsupp ({k - 2} +
          (digits.map fun j => j - 2 : Multiset ℕ)) = _
        rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
        rfl
      rw [hraw, betaDigits_add, a_add, betaDigits_single, ih htail]
      rw [show k - 2 + 2 = k by omega]
      rw [show k = (k - 1) + 1 by omega, golden_phi_pow_a_eq_fib]
      simp only [List.map_cons, List.sum_cons]
      have hk1 : k - 1 + 1 = k := by omega
      have hk2 : k - 1 + 2 = k + 1 := by omega
      simp only [hk1]
      rw [show Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k by
        simpa only [hk1, hk2] using Nat.fib_add_two (n := k - 1)]
      push_cast
      ring

private theorem betaGolden_a (v : ℕ) :
    (betaGolden v).a = (displacementDecode v : ℤ) - v := by
  rw [betaGolden, toRaw, Z, wEncoding]
  change (betaDigits (rawOfZeckendorf (wdigits v))).a = _
  rw [betaDigits_rawOfZeckendorf_a]
  · simp [displacementDecode, decode_wdigits]
  · intro k hk
    exact canonical_two_le (wdigits_isCanonical v) k hk

private theorem betaReal_eq_displacement (v : ℕ) :
    betaReal v = (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenConj := by
  rw [betaReal, embedding_apply, betaGolden_a, betaGolden_b]
  push_cast
  rw [show Real.goldenRatio = 1 - Real.goldenConj by
    linarith [Real.goldenRatio_add_goldenConj]]
  ring

private theorem betaContraction_eq_displacement (v : ℕ) :
    betaContraction v = (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenRatio := by
  have hspread := betaReal_sub_betaContraction v
  rw [betaReal_eq_displacement, ← Real.goldenRatio_sub_goldenConj] at hspread
  linear_combination -hspread

private theorem sum_fib_succ_sub_mul (l : List ℕ) :
    (l.map fun k => (Nat.fib (k + 1) : ℝ) -
      Real.goldenRatio * (Nat.fib k : ℝ)).sum =
      (l.map fun k => Real.goldenConj ^ k).sum := by
  induction l with
  | nil => simp
  | cons k l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Real.fib_succ_sub_goldenRatio_mul_fib, ih]

private theorem pow_add_pow_succ {r : ℝ} (hr : r ^ 2 + r = 1) {a : ℕ} (ha : 1 ≤ a) :
    r ^ a + r ^ (a + 1) = r ^ (a - 1) := by
  conv_lhs =>
    lhs
    rw [show a = a - 1 + 1 by omega, pow_succ]
  conv_lhs =>
    rhs
    rw [show a + 1 = (a - 1) + 2 by omega, pow_add]
  calc
    r ^ (a - 1) * r + r ^ (a - 1) * r ^ 2 =
        r ^ (a - 1) * (r ^ 2 + r) := by ring
    _ = r ^ (a - 1) := by rw [hr, mul_one]

private theorem betaContraction_eq_digit_sum (v : ℕ) :
    betaContraction v = ((wdigits v).map (fun k => Real.goldenConj ^ k)).sum := by
  rw [betaContraction_eq_displacement]
  have hdisp :
      (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenRatio =
        ((wdigits v).map fun k =>
          (Nat.fib (k + 1) : ℝ) - Real.goldenRatio * (Nat.fib k : ℝ)).sum := by
    have hdecode :
        ((wdigits v).map fun k => (Nat.fib k : ℝ)).sum = (v : ℝ) := by
      have hcast : (((wdigits v).map Nat.fib).sum : ℝ) =
          ((wdigits v).map fun k => (Nat.fib k : ℝ)).sum := by
        induction wdigits v with
        | nil => simp
        | cons k l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
      rw [← hcast, decode_wdigits]
    have hdisp_cast :
        (displacementDecode v : ℝ) =
          ((wdigits v).map fun k => (Nat.fib (k + 1) : ℝ)).sum := by
      unfold displacementDecode
      induction wdigits v with
      | nil => simp
      | cons k l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    rw [hdisp_cast, ← hdecode]
    induction wdigits v with
    | nil => simp
    | cons k l ih =>
        simp only [List.map_cons, List.sum_cons]
        linear_combination ih
  rw [hdisp, sum_fib_succ_sub_mul]

private theorem sum_powers_le_sub_head {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d a : ℕ} {l : List ℕ}
    (hgap : (a :: l).Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ k ∈ a :: l, d + 1 ≤ k) :
    ((a :: l).map fun k => r ^ k).sum ≤ r ^ d - r ^ (a + 1) := by
  induction l generalizing a with
  | nil =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [le_sub_iff_add_le, pow_add_pow_succ hr (by have := hmin a (by simp); omega)]
      rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
      have := hmin a (by simp)
      omega
  | cons b l ih =>
      rw [List.pairwise_cons] at hgap
      have hab : b + 2 ≤ a := hgap.1 b (by simp)
      have htail : (b :: l).Pairwise fun x y => y + 2 ≤ x := hgap.2
      have hmin_tail : ∀ k ∈ b :: l, d + 1 ≤ k := by
        intro k hk
        exact hmin k (by simp [hk])
      have hih := ih htail hmin_tail
      simp only [List.map_cons, List.sum_cons]
      calc
        r ^ a + (r ^ b + (l.map fun k => r ^ k).sum) ≤
            r ^ a + (r ^ d - r ^ (b + 1)) := by
              gcongr
              simpa only [List.map_cons, List.sum_cons] using hih
        _ ≤ r ^ d - r ^ (a + 1) := by
          have hpowers : r ^ a + r ^ (a + 1) ≤ r ^ (b + 1) := by
            rw [pow_add_pow_succ hr (by omega)]
            rw [pow_le_pow_iff_right_of_lt_one₀ hr0 hr1]
            omega
          linarith

private theorem sum_powers_lt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hr : r ^ 2 + r = 1) {d : ℕ} {l : List ℕ}
    (hgap : l.Pairwise fun x y => y + 2 ≤ x)
    (hmin : ∀ k ∈ l, d + 1 ≤ k) :
    (l.map fun k => r ^ k).sum < r ^ d := by
  cases l with
  | nil => simpa using pow_pos hr0 d
  | cons a l =>
      refine (sum_powers_le_sub_head hr0 hr1 hr hgap hmin).trans_lt ?_
      exact sub_lt_self _ (pow_pos hr0 (a + 1))

private theorem abs_sum_le_sum_abs : ∀ l : List ℝ, |l.sum| ≤ (l.map abs).sum
  | [] => by simp
  | x :: xs => by
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le x xs.sum).trans
        (add_le_add le_rfl (abs_sum_le_sum_abs xs))

private theorem least_digit_sum_sign {v k : ℕ}
    (hk : k ∈ wdigits v) (hmin : ∀ j ∈ wdigits v, k ≤ j) :
    (0 < ((wdigits v).map (fun j => Real.goldenConj ^ j)).sum ↔ Even k) ∧
      (((wdigits v).map (fun j => Real.goldenConj ^ j)).sum < 0 ↔ Odd k) := by
  let l := wdigits v
  change
    (0 < (l.map (fun j => Real.goldenConj ^ j)).sum ↔ Even k) ∧
      ((l.map (fun j => Real.goldenConj ^ j)).sum < 0 ↔ Odd k)
  have hcanon : l.IsZeckendorfRep := wdigits_isCanonical v
  have hpair : l.Pairwise (fun x y => y + 2 ≤ x) := by
    rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hcanon
    exact (List.pairwise_append.mp hcanon).1
  have hlne : l ≠ [] := by
    intro hnil
    simp [l, hnil] at hk
  have hlast : l.getLast hlne = k := by
    apply le_antisymm
    · by_contra hnot
      have hlast_le := hmin (l.getLast hlne) (List.getLast_mem hlne)
      have hne' : k ≠ l.getLast hlne := by omega
      have hkdrop : k ∈ l.dropLast :=
        List.mem_dropLast_of_mem_of_ne_getLast hk hne'
      have hrel := hpair.rel_dropLast_getLast hkdrop
      omega
    · exact hmin (l.getLast hlne) (List.getLast_mem hlne)
  let pre := l.dropLast
  have hdecomp : pre ++ [k] = l := by
    dsimp [pre]
    simpa [hlast] using (List.dropLast_append_getLast hlne)
  have htail_gap : pre.Pairwise (fun x y => y + 2 ≤ x) :=
    hpair.sublist (List.dropLast_sublist l)
  have htail_min : ∀ j ∈ pre, k + 2 ≤ j := by
    intro j hj
    have hrel := hpair.rel_dropLast_getLast hj
    rw [hlast] at hrel
    exact hrel
  let r : ℝ := Real.goldenRatio⁻¹
  have hr0 : 0 < r := inv_pos.mpr Real.goldenRatio_pos
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hr : r ^ 2 + r = 1 := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hpsi : Real.goldenConj = -r := by
    dsimp [r]
    rw [Real.inv_goldenRatio]
    ring
  have hpow_even : ∀ {n : ℕ}, Even n → Real.goldenConj ^ n = r ^ n := by
    intro n hn
    rw [hpsi, hn.neg_pow]
  have hpow_odd : ∀ {n : ℕ}, Odd n → Real.goldenConj ^ n = -(r ^ n) := by
    intro n hn
    rw [hpsi, hn.neg_pow]
  have htail_abs :
      |(pre.map fun j => Real.goldenConj ^ j).sum| < r ^ (k + 1) := by
    calc
      |(pre.map fun j => Real.goldenConj ^ j).sum| ≤
          (pre.map fun j => |Real.goldenConj ^ j|).sum :=
        by
          simpa only [List.map_map, Function.comp_def] using
            (abs_sum_le_sum_abs (pre.map fun j => Real.goldenConj ^ j))
      _ = (pre.map fun j => r ^ j).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro j hj
        rw [abs_pow, abs_of_neg Real.goldenConj_neg, hpsi]
        simp
      _ < r ^ (k + 1) := by
        apply sum_powers_lt hr0 hr1 hr htail_gap
        intro j hj
        exact htail_min j hj
  have htail_small :
      |(pre.map fun j => Real.goldenConj ^ j).sum| < r ^ k := by
    exact htail_abs.trans (pow_lt_pow_right_of_lt_one₀ hr0 hr1 (by omega))
  have hsum :
      (l.map fun j => Real.goldenConj ^ j).sum =
        Real.goldenConj ^ k + (pre.map fun j => Real.goldenConj ^ j).sum := by
    rw [← hdecomp, List.map_append]
    simp [add_comm]
  have hparity : Even k ∨ Odd k := Nat.even_or_odd k
  constructor
  · constructor
    · intro hpos
      rcases hparity with heven | hodd
      · exact heven
      · rw [hsum, hpow_odd hodd] at hpos
        have htail_upper := (abs_lt.mp htail_small).2
        exfalso
        linarith [pow_pos hr0 k]
    · intro heven
      rw [hsum, hpow_even heven]
      have htail_lower := (abs_lt.mp htail_small).1
      linarith [pow_pos hr0 k]
  · constructor
    · intro hneg
      rcases hparity with heven | hodd
      · rw [hsum, hpow_even heven] at hneg
        have htail_lower := (abs_lt.mp htail_small).1
        exfalso
        linarith [pow_pos hr0 k]
      · exact hodd
    · intro hodd
      rw [hsum, hpow_odd hodd]
      have htail_upper := (abs_lt.mp htail_small).2
      linarith [pow_pos hr0 k]

private theorem betaReal_pos {v : ℕ} (hv : 0 < v) : 0 < betaReal v := by
  rw [betaReal_eq_displacement]
  have hv' : 0 < (v : ℝ) := by exact_mod_cast hv
  have hdisp : 0 ≤ (displacementDecode v : ℝ) := by positivity
  have hpsi : Real.goldenConj < 0 := Real.goldenConj_neg
  nlinarith

theorem betaGolden_norm_sign_of_least_zeckendorf_index
    {v k : ℕ} (hv : 0 < v) (hk : k ∈ wdigits v)
    (hmin : ∀ j ∈ wdigits v, k ≤ j) :
    (0 < norm (betaGolden v) ↔ Even k) ∧
      (norm (betaGolden v) < 0 ↔ Odd k) := by
  have hsign := least_digit_sum_sign hk hmin
  rw [← betaContraction_eq_digit_sum v] at hsign
  have hbeta : 0 < betaReal v := betaReal_pos hv
  have hnorm : (norm (betaGolden v) : ℝ) =
      betaReal v * betaContraction v := by
    symm
    exact embedding_mul_conj (betaGolden v)
  have hnorm_pos : 0 < norm (betaGolden v) ↔
      0 < betaContraction v := by
    constructor
    · intro h
      have h' : 0 < (norm (betaGolden v) : ℝ) := by exact_mod_cast h
      rw [hnorm] at h'
      by_contra hn
      have hle : betaContraction v ≤ 0 := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hbeta.le hle)) h'
    · intro h
      have h' : 0 < (norm (betaGolden v) : ℝ) := by
        rw [hnorm]
        exact mul_pos hbeta h
      exact_mod_cast h'
  have hnorm_neg : norm (betaGolden v) < 0 ↔
      betaContraction v < 0 := by
    constructor
    · intro h
      have h' : (norm (betaGolden v) : ℝ) < 0 := by exact_mod_cast h
      rw [hnorm] at h'
      by_contra hn
      have hle : 0 ≤ betaContraction v := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonneg hbeta.le hle)) h'
    · intro h
      have h' : (norm (betaGolden v) : ℝ) < 0 := by
        rw [hnorm]
        exact mul_neg_of_pos_of_neg hbeta h
      exact_mod_cast h'
  exact ⟨hnorm_pos.trans hsign.1, hnorm_neg.trans hsign.2⟩

#print axioms betaGolden_norm_sign_of_least_zeckendorf_index

end D5.S1.Deficit.Displacement.ZeckendorfNormSign
