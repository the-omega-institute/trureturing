/- GID: D5/S3/ArithSums/A397434ThresholdAnf
   generality: G
   mirror-B: D5/B/S3/ArithSums/A397434ThresholdAnf
   mirror-E: none(waiver:general-symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Adjacent threshold ANF support counts agree exactly at indices two modulo four. -/

import Mathlib

open scoped BigOperators
open Finset

namespace D5.S3.ArithSums.A397434ThresholdAnf

/-- The coefficient obtained by Boolean-lattice Mobius inversion for a
threshold function, grouped by the degree of the squarefree monomial. -/
def thresholdAnfCoeff (t d : Nat) : ZMod 2 :=
  ∑ j ∈ Icc t d, (d.choose j : ZMod 2)

/-- The `0`/`1` representative of the literature formula for a positive
threshold, extended at threshold zero by the constant-true function. -/
def reducedCoeffBit (t d : Nat) : Nat :=
  if t = 0 then if d = 0 then 1 else 0
  else if d = 0 then 0 else (d - 1).choose (t - 1) % 2

/-- Squarefree monomials are indexed by subsets of the variables. -/
def thresholdAnfSupport (n t : Nat) : Finset (Finset (Fin n)) :=
  Finset.univ.powerset.filter fun monomial => reducedCoeffBit t monomial.card = 1

/-- The number of supported monomials, grouped by degree. -/
def thresholdMonomialCount (n t : Nat) : Nat :=
  ∑ d ∈ range (n + 1), n.choose d * reducedCoeffBit t d

/-- OEIS A397434, with `ceil (n / 2) = (n + 1) / 2`. -/
def a (n : Nat) : Nat :=
  thresholdMonomialCount n ((n + 1) / 2)

private theorem lower_choose_sum_mod_two (d t : Nat) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    (∑ j ∈ range t, (d.choose j : ZMod 2)) =
      ((d - 1).choose (t - 1) : ZMod 2) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ht
  have h := Int.alternating_sum_range_choose_eq_choose (n := d) (m := t)
  have h' := congrArg (fun z : Int => (z : ZMod 2)) h
  simpa [Nat.add_comm] using h'

/-- Local implementation of Meaux (2021), Lemma 2, attributed there to
Meaux (2019), Theorem 1. -/
theorem threshold_anf_coefficient_reduction (t d : Nat)
    (ht : 1 ≤ t) (hd : 1 ≤ d) :
    thresholdAnfCoeff t d = ((d - 1).choose (t - 1) : ZMod 2) := by
  by_cases hdt : d < t
  · have hsub : d - 1 < t - 1 := by omega
    simp [thresholdAnfCoeff, Icc_eq_empty_of_lt hdt, Nat.choose_eq_zero_of_lt hsub]
  · have htd : t ≤ d := Nat.le_of_not_gt hdt
    have hsplit := Finset.sum_range_add_sum_Ico
      (f := fun j => (d.choose j : ZMod 2)) (show t ≤ d + 1 by omega)
    have htotal : (∑ j ∈ range (d + 1), (d.choose j : ZMod 2)) = 0 := by
      have h := congrArg (fun n : Nat => (n : ZMod 2)) (Nat.sum_range_choose d)
      simpa [show (2 : ZMod 2) = 0 by decide, show d ≠ 0 by omega] using h
    have hinterval : Ico t (d + 1) = Icc t d := by
      ext j
      simp
    have hparts :
        (∑ j ∈ range t, (d.choose j : ZMod 2)) + thresholdAnfCoeff t d = 0 := by
      rw [thresholdAnfCoeff, ← hinterval]
      exact hsplit.trans htotal
    calc
      thresholdAnfCoeff t d = -(∑ j ∈ range t, (d.choose j : ZMod 2)) :=
        eq_neg_of_add_eq_zero_right hparts
      _ = ∑ j ∈ range t, (d.choose j : ZMod 2) := by simp
      _ = ((d - 1).choose (t - 1) : ZMod 2) :=
        lower_choose_sum_mod_two d t hd ht

private theorem reducedCoeffBit_zero_or_one (t d : Nat) :
    reducedCoeffBit t d = 0 ∨ reducedCoeffBit t d = 1 := by
  by_cases ht : t = 0
  · by_cases hd : d = 0 <;> simp [reducedCoeffBit, ht, hd]
  · by_cases hd : d = 0
    · simp [reducedCoeffBit, ht, hd]
    · simpa [reducedCoeffBit, ht, hd] using
        Nat.mod_two_eq_zero_or_one ((d - 1).choose (t - 1))

theorem threshold_support_card (n t : Nat) :
    (thresholdAnfSupport n t).card = thresholdMonomialCount n t := by
  classical
  rw [thresholdAnfSupport, thresholdMonomialCount, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  have hpoint (s : Finset (Fin n)) :
      (if reducedCoeffBit t s.card = 1 then 1 else 0) = reducedCoeffBit t s.card := by
    rcases reducedCoeffBit_zero_or_one t s.card with h | h <;> simp [h]
  simp_rw [hpoint]
  simpa [nsmul_eq_mul, mul_comm] using
    (Finset.sum_powerset_apply_card (f := fun d => reducedCoeffBit t d)
      (x := (Finset.univ : Finset (Fin n))))

/-- The OEIS sequence value is the cardinality of the threshold ANF support. -/
theorem a_eq_threshold_support_card (n : Nat) :
    a n = (thresholdAnfSupport n ((n + 1) / 2)).card := by
  exact (threshold_support_card n ((n + 1) / 2)).symm

/-- The parity bit used by the two adjacent rows with threshold `m + 1`. -/
def pBit (m d : Nat) : Nat :=
  reducedCoeffBit (m + 1) d

@[simp] private theorem pBit_zero (m : Nat) : pBit m 0 = 0 := by
  simp [pBit, reducedCoeffBit]

@[simp] private theorem pBit_succ (m d : Nat) :
    pBit m (d + 1) = d.choose m % 2 := by
  simp [pBit, reducedCoeffBit]

private theorem pBit_zero_or_one (m d : Nat) : pBit m d = 0 ∨ pBit m d = 1 :=
  reducedCoeffBit_zero_or_one (m + 1) d

/-- The degree-grouped monomial count, coerced to the integers. -/
def rowSumZ (n : Nat) (b : Nat → Nat) : Int :=
  ∑ d ∈ range (n + 1), (n.choose d : Int) * b d

private theorem thresholdMonomialCount_cast (n t : Nat) :
    (thresholdMonomialCount n t : Int) = rowSumZ n (reducedCoeffBit t) := by
  simp [thresholdMonomialCount, rowSumZ]

private theorem a_odd_row (m : Nat) :
    (a (2 * m + 1) : Int) = rowSumZ (2 * m + 1) (pBit m) := by
  rw [a_eq_threshold_support_card, threshold_support_card, thresholdMonomialCount_cast]
  have ht : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [ht]
  rfl

private theorem a_even_succ_row (m : Nat) :
    (a (2 * m + 2) : Int) = rowSumZ (2 * m + 2) (pBit m) := by
  rw [a, thresholdMonomialCount_cast]
  have ht : (2 * m + 2 + 1) / 2 = m + 1 := by omega
  rw [ht]
  rfl

private theorem a_even_row (m : Nat) (hm : 1 ≤ m) :
    (a (2 * m) : Int) = rowSumZ (2 * m) (pBit (m - 1)) := by
  rw [a_eq_threshold_support_card, threshold_support_card, thresholdMonomialCount_cast]
  have ht : (2 * m + 1) / 2 = (m - 1) + 1 := by omega
  rw [ht]
  rfl

private theorem rowSumZ_succ (n : Nat) (b : Nat → Nat) :
    rowSumZ (n + 1) b = rowSumZ n b + rowSumZ n (fun d => b (d + 1)) := by
  simpa [rowSumZ] using
    (Finset.sum_choose_succ_mul (R := Int) (fun i _ => (b i : Int)) n)

private theorem mod_two_recover (x y : Nat) :
    ((x % 2 : Nat) : Int) = ((y % 2 : Nat) : Int) + (((x + y) % 2 : Nat) : Int) -
      2 * ((y % 2 : Nat) : Int) * (((x + y) % 2 : Nat) : Int) := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  all_goals rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  all_goals norm_num [Nat.add_mod, hx, hy]

private theorem pBit_pascal (m : Nat) (hm : 1 ≤ m) (d : Nat) :
    (pBit (m - 1) d : Int) =
      (pBit m d : Int) + (pBit m (d + 1) : Int) -
        2 * (pBit m d : Int) * (pBit m (d + 1) : Int) := by
  cases d with
  | zero => simp [pBit, reducedCoeffBit, Nat.choose_eq_zero_of_lt hm]
  | succ d =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
      simpa [Nat.choose_succ_succ, Nat.one_add] using
        mod_two_recover (d.choose m) (d.choose (m + 1))

def S (m : Nat) : Finset Nat :=
  (Icc 1 (2 * m)).filter fun d => Odd ((d - 1).choose m) ∧ Odd (d.choose m)

private theorem odd_iff_mod_two_eq_one (n : Nat) : Odd n ↔ n % 2 = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    omega
  · intro h
    exact ⟨n / 2, by omega⟩

private theorem product_eq_indicator_S (m d : Nat) (hd : d ∈ Icc 1 (2 * m)) :
    (pBit m d : Int) * pBit m (d + 1) = if d ∈ S m then 1 else 0 := by
  have hd1 := (mem_Icc.mp hd).1
  have hd0 : d ≠ 0 := by omega
  have hx := Nat.mod_two_eq_zero_or_one ((d - 1).choose m)
  have hy := Nat.mod_two_eq_zero_or_one (d.choose m)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp [S, hd, pBit, reducedCoeffBit, hd0, odd_iff_mod_two_eq_one, hx, hy]

private theorem weighted_product_sum_eq_S (m : Nat) :
    (∑ d ∈ range (2 * m + 1),
        (Nat.choose (2 * m) d : Int) * pBit m d * pBit m (d + 1)) =
      ∑ d ∈ S m, (Nat.choose (2 * m) d : Int) := by
  calc
    _ = ∑ d ∈ range (2 * m + 1),
          if d ∈ S m then (Nat.choose (2 * m) d : Int) else 0 := by
        apply sum_congr rfl
        intro d hd
        have hdIcc : d ∈ Icc 1 (2 * m) ∨ d = 0 := by
          simp only [mem_range] at hd
          by_cases hd0 : d = 0
          · exact Or.inr hd0
          · left
            simp
            omega
        rcases hdIcc with hdIcc | rfl
        · rw [mul_assoc, product_eq_indicator_S m d hdIcc]
          simp
        · simp [S]
    _ = ∑ d ∈ (range (2 * m + 1)).filter (fun d => d ∈ S m),
          (Nat.choose (2 * m) d : Int) := by
        rw [sum_filter]
    _ = ∑ d ∈ S m, (Nat.choose (2 * m) d : Int) := by
        congr 1
        ext d
        simp [S]
        omega

private theorem row_bridge (m : Nat) (hm : 1 ≤ m) :
    rowSumZ (2 * m + 1) (pBit m) - rowSumZ (2 * m) (pBit (m - 1)) =
      2 * ∑ d ∈ S m, (Nat.choose (2 * m) d : Int) := by
  rw [show 2 * m + 1 = 2 * m + 1 by rfl, rowSumZ_succ]
  rw [← weighted_product_sum_eq_S]
  simp only [rowSumZ]
  simp_rw [pBit_pascal m hm]
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  ring_nf
  rw [Finset.sum_mul]

/-- The exact integer difference bridge at a positive even index. -/
theorem anf_count_even_bridge (m : Nat) (hm : 1 ≤ m) :
    (a (2 * m + 1) : Int) - a (2 * m) =
      2 * ∑ d ∈ S m, (Nat.choose (2 * m) d : Int) := by
  rw [a_odd_row, a_even_row m hm]
  exact row_bridge m hm

private theorem choose_even_of_even_top_odd_bottom {n k : Nat}
    (hn : Even n) (hk : Odd k) : Even (n.choose k) := by
  have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := n) (k := k) (p := 2)
  have hl' : n.choose k % 2 =
      ((n % 2).choose (k % 2) * (n / 2).choose (k / 2)) % 2 := by
    simpa [Nat.ModEq] using hl
  have hn0 := Nat.even_iff.mp hn
  have hk1 := (odd_iff_mod_two_eq_one k).mp hk
  apply Nat.even_iff.mpr
  rw [hl', hn0, hk1]
  simp

private theorem choose_odd_forces_top_odd {n k : Nat}
    (hk : Odd k) (hchoose : Odd (n.choose k)) : Odd n := by
  have hnBit := Nat.mod_two_eq_zero_or_one n
  rcases hnBit with hn0 | hn1
  · have hnEven : Even n := Nat.even_iff.mpr hn0
    exact False.elim ((Nat.not_even_iff_odd.mpr hchoose)
      (choose_even_of_even_top_odd_bottom hnEven hk))
  · exact (odd_iff_mod_two_eq_one n).mpr hn1

/-- Odd parity forces the adjacent-binomial support set to be empty. -/
theorem S_empty_of_odd (m : Nat) (hm : Odd m) : S m = ∅ := by
  ext d
  constructor
  · intro hd
    exfalso
    rcases mem_filter.mp hd with ⟨hdRange, hPrevious, hCurrent⟩
    have hdOdd : Odd d := choose_odd_forces_top_odd hm hCurrent
    have hdMod := (odd_iff_mod_two_eq_one d).mp hdOdd
    have hPredEven : Even (d - 1) := Nat.even_iff.mpr (by omega)
    have hChooseEven : Even ((d - 1).choose m) :=
      choose_even_of_even_top_odd_bottom hPredEven hm
    exact (Nat.not_even_iff_odd.mpr hPrevious) hChooseEven
  · simp

/-- Positive even parity puts `m + 1` in the adjacent-binomial support set. -/
theorem mem_S_of_even (m : Nat) (hm : 1 ≤ m) (hmEven : Even m) : m + 1 ∈ S m := by
  have hm0 := Nat.even_iff.mp hmEven
  have hlt : m < 2 * m := by omega
  have hSuccOdd : Odd (m + 1) := (odd_iff_mod_two_eq_one (m + 1)).mpr (by omega)
  simp [S, hlt, hSuccOdd, Nat.choose_succ_self_right]

/-- The `d = 2m` endpoint is present in the domain but never in `S m` for `m ≥ 1`. -/
theorem endpoint_not_mem_S (m : Nat) (hm : 1 ≤ m) : 2 * m ∉ S m := by
  intro hmem
  have hOdd := (mem_filter.mp hmem).2.2
  have hEven : Even ((2 * m).choose m) :=
    even_iff_two_dvd.mpr (Nat.two_dvd_centralBinom_of_one_le hm)
  exact (Nat.not_even_iff_odd.mpr hOdd) hEven

private theorem shifted_row_pos (m : Nat) :
    0 < rowSumZ (2 * m + 1) (fun d => pBit m (d + 1)) := by
  rw [rowSumZ]
  refine Finset.sum_pos'
    (fun _ _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) ?_
  refine ⟨m, by simp; omega, ?_⟩
  simp [pBit_succ, Nat.choose_pos (show m ≤ 2 * m + 1 by omega)]

/-- Adjacent counts at an odd index are strictly increasing, including `m = 0`. -/
theorem odd_step_strict (m : Nat) : a (2 * m + 1) < a (2 * m + 2) := by
  have hrow :
      rowSumZ (2 * m + 2) (pBit m) =
        rowSumZ (2 * m + 1) (pBit m) +
          rowSumZ (2 * m + 1) (fun d => pBit m (d + 1)) := by
    have h := rowSumZ_succ (2 * m + 1) (pBit m)
    rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega] at h
    exact h
  have hInt : (a (2 * m + 1) : Int) < (a (2 * m + 2) : Int) := by
    rw [a_odd_row, a_even_succ_row, hrow]
    exact lt_add_of_pos_right _ (shifted_row_pos m)
  exact_mod_cast hInt

private theorem even_step_eq_of_odd (m : Nat) (hm : 1 ≤ m) (hmOdd : Odd m) :
    a (2 * m) = a (2 * m + 1) := by
  have h := anf_count_even_bridge m hm
  rw [S_empty_of_odd m hmOdd] at h
  simp only [sum_empty, mul_zero] at h
  have hInt : (a (2 * m) : Int) = (a (2 * m + 1) : Int) := by omega
  exact_mod_cast hInt

private theorem even_step_strict_of_even (m : Nat) (hm : 1 ≤ m) (hmEven : Even m) :
    a (2 * m) < a (2 * m + 1) := by
  have hmem : m + 1 ∈ S m := mem_S_of_even m hm hmEven
  have hle : m + 1 ≤ 2 * m := (mem_Icc.mp (mem_filter.mp hmem).1).2
  have hne : m + 1 ≠ 2 * m := by
    intro heq
    exact endpoint_not_mem_S m hm (heq ▸ hmem)
  have hlt : m + 1 < 2 * m := lt_of_le_of_ne hle hne
  have hsum : 0 < ∑ d ∈ S m, (Nat.choose (2 * m) d : Int) := by
    refine Finset.sum_pos' (fun _ _ => Int.natCast_nonneg _) ?_
    refine ⟨m + 1, hmem, ?_⟩
    exact Int.ofNat_lt.mpr (Nat.choose_pos (Nat.le_of_lt hlt))
  have hdiff :
      0 < (a (2 * m + 1) : Int) - (a (2 * m) : Int) := by
    rw [anf_count_even_bridge m hm]
    positivity
  exact_mod_cast (sub_pos.mp hdiff)

/-- At a positive even index `2m`, equality holds exactly when `m` is odd. -/
theorem even_step_eq_iff (m : Nat) (hm : 1 ≤ m) :
    a (2 * m) = a (2 * m + 1) ↔ Odd m := by
  constructor
  · intro heq
    rcases m.even_or_odd with hmEven | hmOdd
    · exact False.elim ((Nat.ne_of_lt (even_step_strict_of_even m hm hmEven)) heq)
    · exact hmOdd
  · exact even_step_eq_of_odd m hm

/-- OEIS A397434: from index one onward, adjacent counts agree exactly at
indices congruent to two modulo four. -/
theorem a_eq_succ_iff_mod_four (n : Nat) (hn : 1 ≤ n) :
    a n = a (n + 1) ↔ n % 4 = 2 := by
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · subst n
    have hmPos : 1 ≤ m := by omega
    constructor
    · intro heq
      have hmOdd := (even_step_eq_iff m hmPos).mp (by simpa using heq)
      have hmMod := (odd_iff_mod_two_eq_one m).mp hmOdd
      omega
    · intro hmod
      apply (even_step_eq_iff m hmPos).mpr
      apply (odd_iff_mod_two_eq_one m).mpr
      omega
  · subst n
    constructor
    · intro heq
      have hlt := odd_step_strict m
      rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega] at heq
      have heq' : a (2 * m + 1) = a (2 * m + 2) := heq
      exact False.elim ((Nat.ne_of_lt hlt) heq')
    · intro hmod
      omega

end D5.S3.ArithSums.A397434ThresholdAnf
