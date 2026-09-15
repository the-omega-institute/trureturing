/- GID: D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation
   generality: I
   mirror-B: D5/B/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.claim; result=D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.result; claim=D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.claim
   digest: A negative real divisor-power record refutes the highly-or-deeply-composite union. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- SPDX-License-Identifier: Apache-2.0 -/

open scoped BigOperators
open Finset ArithmeticFunction

namespace D5.S3.ArithSums.DivisorRecords.DivisorPowerUnionRefutation

noncomputable def DivisorPowerSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ) ^ x

def StrictDivisorPowerRecord (n : ℕ) (x : ℝ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n →
    DivisorPowerSum m x < DivisorPowerSum n x

def claim : Prop :=
  ∀ n : ℕ, 0 < n →
    ((∃ x : ℝ, x ≤ 0 ∧ StrictDivisorPowerRecord n x) ↔
      (StrictDivisorPowerRecord n 0 ∨
        ∃ B : ℝ, B < 0 ∧ ∀ x : ℝ, x ≤ B →
          StrictDivisorPowerRecord n x))

theorem result : ¬ claim := by
  have hpow (d : ℕ) : (d : ℝ) ^ (-4 : ℝ) = 1 / (d : ℝ) ^ 4 := by
    norm_num [Real.rpow_neg_natCast]
  have hsigma (n : ℕ) (hn : 0 < n) :
      DivisorPowerSum n (-4) = (ArithmeticFunction.sigma 4 n : ℝ) / (n : ℝ)^4 := by
    unfold DivisorPowerSum
    rw [ArithmeticFunction.sigma_eq_sum_div]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
    rw [hpow]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hstep (r : ℝ) (hr : 1 ≤ r) :
      1 / (r + 1)^4 + 1 / (3 * (r + 1)^3) ≤ 1 / (3 * r^3) := by
    have hr0 : 0 < r := by linarith
    have hr1 : 0 < r + 1 := by linarith
    field_simp
    nlinarith [sq_nonneg r, pow_nonneg hr0.le 3]
  have hupper (r : ℕ) (hr : 64 ≤ r) :
      (∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1)^4) + 1 / (3 * (r : ℝ)^3) ≤
        (∑ i ∈ Finset.range 64, 1 / ((i : ℝ) + 1)^4) + 1 / (3 * (64 : ℝ)^3) := by
    induction r, hr using Nat.le_induction with
    | base => rfl
    | succ r hr ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have hs := hstep (r : ℝ) (by exact_mod_cast (show 1 ≤ r by omega))
      linarith
  have hnum : (∑ i ∈ Finset.range 64, 1 / ((i : ℝ) + 1)^4) +
      1 / (3 * (64 : ℝ)^3) < 108232327 / 100000000 := by
    norm_num [Finset.sum_range_succ]
  have hbound (s : Finset ℕ) (hs : ∀ d ∈ s, 0 < d) :
      (∑ d ∈ s, 1 / (d : ℝ)^4) < 108232327 / 100000000 := by
    let r := max 64 (s.sup id)
    have hr : 64 ≤ r := le_max_left _ _
    have hsub : s ⊆ Finset.Icc 1 r := by
      intro d hd
      exact Finset.mem_Icc.mpr ⟨hs d hd, (Finset.le_sup (f := id) hd).trans (le_max_right _ _)⟩
    have heq : (∑ d ∈ Finset.Icc 1 r, 1 / (d : ℝ)^4) =
        ∑ i ∈ Finset.range r, 1 / ((i : ℝ) + 1)^4 := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    have hle : (∑ d ∈ s, 1 / (d : ℝ)^4) ≤
        ∑ d ∈ Finset.Icc 1 r, 1 / (d : ℝ)^4 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    rw [heq] at hle
    have ht : 0 ≤ 1 / (3 * (r : ℝ)^3) := by positivity
    have hu := hupper r hr
    linarith
  let value (l : List (ℕ × ℕ)) : ℕ := (l.map (fun pe => pe.1 ^ pe.2)).prod
  let sig (k : ℕ) (l : List (ℕ × ℕ)) : ℕ :=
    (l.map (fun pe => ∑ j ∈ Finset.range (pe.2 + 1), pe.1 ^ (j*k))).prod
  have hsnd (k : ℕ) (l : List (ℕ × ℕ))
      (hp : ∀ pe ∈ l, Nat.Prime pe.1)
      (hc : l.Pairwise (fun a b => Nat.Coprime (a.1^a.2) (b.1^b.2))) :
      ArithmeticFunction.sigma k (value l) = sig k l := by
    induction l with
    | nil => simp [value,sig]
    | cons pe tail ih =>
      have hpt : ∀ a ∈ tail, Nat.Prime a.1 := fun a ha => hp a (List.mem_cons_of_mem pe ha)
      obtain ⟨hcop,hct⟩ := List.pairwise_cons.mp hc
      have hcop' : Nat.Coprime (pe.1^pe.2) (value tail) := by
        apply Nat.coprime_list_prod_right_iff.mpr
        intro z hz
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
        exact hcop a ha
      change ArithmeticFunction.sigma k (pe.1^pe.2 * value tail) = _
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop',
        ArithmeticFunction.sigma_apply_prime_pow (hp pe (by simp)), ih hpt hct]
      rfl
  have hNσ : sigma 4 32125373280 = 1152780338446808124302790430032176310391296 := by
    let l : List (ℕ × ℕ) := [(2,5), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (23,1)]
    have hv := hsnd 4 l (by norm_num [l]) (by decide +kernel)
    norm_num [value, sig, l, Finset.sum_range_succ] at hv
    exact hv
  have hN4 : DivisorPowerSum 32125373280 (-4) =
      1678677187106139216341549972195017 / 1551005573419488074754054309120000 := by
    rw [hsigma _ (by norm_num), hNσ]
    norm_num
  have hforce (m : ℕ) (hm : 0 < m) (hnot : ¬ 232792560 ∣ m) :
      DivisorPowerSum m (-4) < DivisorPowerSum 32125373280 (-4) := by
    obtain ⟨d, hd, hdm⟩ : ∃ d ∈ Finset.Icc 1 19, ¬ d ∣ m := by
      by_contra h
      push Not at h
      apply hnot
      have hl : (Finset.Icc 1 19).lcm id ∣ m := Finset.lcm_dvd h
      have he : (Finset.Icc 1 19).lcm id = 232792560 := by decide
      rwa [he] at hl
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdle : d ≤ 19 := (Finset.mem_Icc.mp hd).2
    have hdmem : d ∉ m.divisors := fun hh => hdm (Nat.dvd_of_mem_divisors hh)
    have hd2mem : 2*d ∉ m.divisors := by
      intro hh
      exact hdm (dvd_trans (dvd_mul_left d 2) (Nat.dvd_of_mem_divisors hh))
    have hne : d ≠ 2*d := by omega
    have hs := hbound (insert d (insert (2*d) m.divisors)) (by
      intro e he
      simp only [Finset.mem_insert] at he
      rcases he with rfl | rfl | he
      · exact hdpos
      · omega
      · exact Nat.pos_of_mem_divisors he)
    rw [sum_insert (by simp only [mem_insert, not_or]; exact ⟨hne,hdmem⟩), sum_insert hd2mem] at hs
    have hweights : 1 / (19 : ℝ)^4 + 1 / (38 : ℝ)^4 ≤
        1 / (d : ℝ)^4 + 1 / ((2*d : ℕ) : ℝ)^4 := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hdRle : (d : ℝ) ≤ 19 := by exact_mod_cast hdle
      have hd2R : (0 : ℝ) < (2*d : ℕ) := by exact_mod_cast (show 0 < 2*d by omega)
      have hd2Rle : ((2*d : ℕ) : ℝ) ≤ 38 := by exact_mod_cast (show 2*d ≤ 38 by omega)
      exact add_le_add (one_div_le_one_div_of_le (pow_pos hdR 4) (pow_le_pow_left₀ hdR.le hdRle 4))
        (one_div_le_one_div_of_le (pow_pos hd2R 4) (pow_le_pow_left₀ hd2R.le hd2Rle 4))
    have he : (∑ d ∈ m.divisors, 1 / (d : ℝ)^4) = DivisorPowerSum m (-4) := by
      simp only [DivisorPowerSum,hpow]
    rw [he] at hs
    rw [hN4]
    norm_num at hweights hs ⊢
    linarith
  let data : List (List (ℕ × ℕ)) := [
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,7), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,4), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,6), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,8), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,2), (19,1)],
    [(2,5), (3,4), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,2)],
    [(2,6), (3,2), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (23,1)],
    [(2,7), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,3), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,4), (3,5), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,6), (3,2), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (29,1)],
    [(2,5), (3,3), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (31,1)],
    [(2,9), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,2), (19,1)],
    [(2,4), (3,2), (5,2), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,6), (3,4), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (37,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,2)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,7), (3,2), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (41,1)],
    [(2,5), (3,3), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (43,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,4), (3,4), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (23,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (47,1)],
    [(2,8), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,3), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,3), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,2), (19,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (53,1)],
    [(2,5), (3,5), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,2), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,7), (3,2), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,2)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (29,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (59,1)],
    [(2,6), (3,3), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (61,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (31,1)],
    [(2,4), (3,4), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,10), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,2), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,5), (3,3), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (67,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,1), (13,1), (17,2), (19,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (23,1)],
    [(2,5), (3,2), (5,2), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (71,1)],
    [(2,7), (3,4), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (73,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (37,1)],
    [(2,4), (3,3), (5,3), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,2)],
    [(2,4), (3,2), (5,1), (7,2), (11,2), (13,1), (17,1), (19,1)],
    [(2,5), (3,3), (5,1), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (79,1)],
    [(2,8), (3,2), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,6), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (41,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (83,1)],
    [(2,6), (3,3), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,2), (7,1), (11,1), (13,1), (17,2), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (43,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (29,1)],
    [(2,7), (3,2), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (89,1)],
    [(2,5), (3,4), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,2), (11,1), (13,2), (17,1), (19,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (23,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (31,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (47,1)],
    [(2,4), (3,2), (5,2), (7,1), (11,1), (13,1), (17,1), (19,2)],
    [(2,9), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (97,1)],
    [(2,5), (3,2), (5,1), (7,3), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,4), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,6), (3,2), (5,3), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (101,1)],
    [(2,5), (3,3), (5,1), (7,1), (11,1), (13,1), (17,2), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (103,1)],
    [(2,7), (3,2), (5,1), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,4), (3,3), (5,2), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (53,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (107,1)],
    [(2,6), (3,5), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (109,1)],
    [(2,5), (3,2), (5,2), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (37,1)],
    [(2,8), (3,2), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (113,1)],
    [(2,5), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,2)],
    [(2,4), (3,2), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1), (23,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (29,1)],
    [(2,4), (3,4), (5,1), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (59,1)],
    [(2,4), (3,2), (5,1), (7,2), (11,1), (13,1), (17,2), (19,1)],
    [(2,7), (3,3), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,3), (13,1), (17,1), (19,1)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (61,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (41,1)],
    [(2,6), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (31,1)],
    [(2,4), (3,2), (5,4), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,5), (3,4), (5,1), (7,2), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (127,1)],
    [(2,11), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,4), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (43,1)],
    [(2,5), (3,2), (5,2), (7,1), (11,1), (13,2), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (131,1)],
    [(2,6), (3,3), (5,1), (7,1), (11,2), (13,1), (17,1), (19,1)],
    [(2,4), (3,2), (5,1), (7,2), (11,1), (13,1), (17,1), (19,2)],
    [(2,5), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (67,1)],
    [(2,4), (3,5), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)],
    [(2,7), (3,2), (5,1), (7,1), (11,1), (13,1), (17,2), (19,1)],
    [(2,4), (3,2), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (137,1)]  ]
  have hchecks : ∀ i : Fin 137,
      let l := data.getD i.val []
      (∀ pe ∈ l, Nat.Prime pe.1) ∧
      l.Pairwise (fun a b => Nat.Coprime (a.1^a.2) (b.1^b.2)) ∧
      value l = 232792560 * (i.val+1) ∧
      sig 4 l * 32125373280^4 <
        1152780338446808124302790430032176310391296 * (232792560 * (i.val+1))^4 := by
    decide +kernel
  have hrecord : StrictDivisorPowerRecord 32125373280 (-4) := by
    refine ⟨by norm_num, ?_⟩
    intro m hm hmlt
    by_cases hdiv : 232792560 ∣ m
    · obtain ⟨k,rfl⟩ := hdiv
      have hkpos : 1 ≤ k := by omega
      have hklt : k ≤ 137 := by omega
      let i : Fin 137 := ⟨k-1, by omega⟩
      have hi : i.val+1=k := by dsimp [i]; omega
      obtain ⟨hp,hc,hval,hineq⟩ := hchecks i
      rw [hi] at hval hineq
      have hv := hsnd 4 (data.getD i.val []) hp hc
      rw [hval] at hv
      rw [hsigma _ hm, hsigma _ (by norm_num), hNσ, hv]
      have hmR : (0 : ℝ) < (232792560*k : ℕ) := by exact_mod_cast hm
      apply (div_lt_div_iff₀ (pow_pos hmR 4) (pow_pos (by norm_num : (0 : ℝ) < 32125373280) 4)).mpr
      exact_mod_cast hineq
    · exact hforce m hm hdiv
  have hzero (n : ℕ) : DivisorPowerSum n 0 = (ArithmeticFunction.sigma 0 n : ℝ) := by
    simp [DivisorPowerSum,ArithmeticFunction.sigma_apply]
  have hNzero : ArithmeticFunction.sigma 0 32125373280 = 3072 := by
    let l : List (ℕ × ℕ) := [(2,5), (3,3), (5,1), (7,1), (11,1), (13,1), (17,1), (19,1), (23,1)]
    have hv := hsnd 0 l (by norm_num [l]) (by decide +kernel)
    norm_num [value, sig, l, Finset.sum_range_succ] at hv
    exact hv
  have hHzero : ArithmeticFunction.sigma 0 27935107200 = 3072 := by
    let l : List (ℕ × ℕ) := [(2,7), (3,3), (5,2), (7,1), (11,1), (13,1), (17,1), (19,1)]
    have hv := hsnd 0 l (by norm_num [l]) (by decide +kernel)
    norm_num [value, sig, l, Finset.sum_range_succ] at hv
    exact hv
  have hnotzero : ¬ StrictDivisorPowerRecord 32125373280 0 := by
    intro hh
    have ht := hh.2 27935107200 (by norm_num) (by norm_num)
    rw [hzero,hzero,hNzero,hHzero] at ht
    exact lt_irrefl _ ht
  have hprefix : ∀ d ∈ Finset.Icc 1 26, d ∣ 32125373280 → d ∣ 26771144400 := by
    decide +kernel
  have hnotdeep : ¬ ∃ B : ℝ, B < 0 ∧ ∀ x : ℝ, x ≤ B →
      StrictDivisorPowerRecord 32125373280 x := by
    rintro ⟨B,hB,hrec⟩
    let x := min B (-1000)
    have hxB : x ≤ B := min_le_left _ _
    have hx1000 : x ≤ -1000 := min_le_right _ _
    have hx0 : x ≤ 0 := hxB.trans hB.le
    have hbeat := (hrec x hxB).2 26771144400 (by norm_num) (by norm_num)
    have hsmall : ∀ d ∈ (32125373280).divisors \ (26771144400).divisors, 27 ≤ d := by
      intro d hd
      obtain ⟨hdn,hdm⟩ := Finset.mem_sdiff.mp hd
      by_contra h
      have hdpos := Nat.pos_of_mem_divisors hdn
      have hdm' := hprefix d (Finset.mem_Icc.mpr ⟨hdpos,by omega⟩) (Nat.dvd_of_mem_divisors hdn)
      exact hdm (Nat.mem_divisors.mpr ⟨hdm',by norm_num⟩)
    have hsumN : (∑ d ∈ (32125373280).divisors \ (26771144400).divisors, ((d : ℕ) : ℝ)^x) ≤
        (32125373280 : ℝ) * (27 : ℝ)^x := by
      calc
        _ ≤ ∑ _d ∈ (32125373280).divisors \ (26771144400).divisors, (27 : ℝ)^x := by
          apply Finset.sum_le_sum
          intro d hd
          exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hsmall d hd) hx0
        _ = (((32125373280).divisors \ (26771144400).divisors).card : ℝ) * (27 : ℝ)^x := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (32125373280 : ℝ) * (27 : ℝ)^x := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num) x)
          exact_mod_cast (card_le_card (show (32125373280).divisors \ (26771144400).divisors ⊆
            (32125373280).divisors from Finset.sdiff_subset)).trans (Nat.card_divisors_le_self _)
    have hsumM : (25 : ℝ)^x ≤
        ∑ d ∈ (26771144400).divisors \ (32125373280).divisors, ((d : ℕ) : ℝ)^x := by
      apply Finset.single_le_sum (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) x)
      norm_num [Finset.mem_sdiff,Nat.mem_divisors]
    have hratio0 : (32125373280 : ℝ) * (27 / 25 : ℝ)^(-1000 : ℝ) < 1 := by
      have hten : (2 : ℝ) < (27/25 : ℝ)^(10 : ℕ) := by norm_num
      have hhundred := pow_lt_pow_left₀ hten (by norm_num : (0 : ℝ) ≤ 2) (by decide : (100 : ℕ) ≠ 0)
      rw [← pow_mul] at hhundred
      have hlarge : (32125373280 : ℝ) < (27/25 : ℝ)^(1000 : ℕ) := by
        norm_num only [Nat.reduceMul] at hhundred
        exact lt_trans (by norm_num) hhundred
      rw [show (-1000 : ℝ) = -(1000 : ℕ) by norm_num,Real.rpow_neg_natCast,zpow_neg,zpow_natCast]
      rw [← div_eq_mul_inv]
      exact (div_lt_one (pow_pos (by norm_num : (0 : ℝ) < 27/25) 1000)).mpr hlarge
    have hratio : (32125373280 : ℝ) * (27 / 25 : ℝ)^x < 1 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 27/25) hx1000
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh (by norm_num)) hratio0
    have hstrict : (32125373280 : ℝ) * (27 : ℝ)^x < (25 : ℝ)^x := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 27) (by norm_num : (0 : ℝ) ≤ 25)] at hratio
      have hp25 : (0 : ℝ) < 25^x := Real.rpow_pos_of_pos (by norm_num) x
      apply (div_lt_one hp25).mp
      simpa only [mul_div_assoc] using hratio
    have hbalance := Finset.sum_sdiff_sub_sum_sdiff
      (s₁ := (26771144400).divisors) (s₂ := (32125373280).divisors)
      (f := fun d : ℕ => (d : ℝ)^x)
    change _ = DivisorPowerSum 32125373280 x - DivisorPowerSum 26771144400 x at hbalance
    linarith
  intro hclaim
  have hright := (hclaim 32125373280 (by norm_num)).mp ⟨-4,by norm_num,hrecord⟩
  exact hright.elim hnotzero hnotdeep

end D5.S3.ArithSums.DivisorRecords.DivisorPowerUnionRefutation
