/- GID: D5/S1/Words/GoldenFactorSecondOrderBinomialRigidity
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: First-letter count and the scattered true-false count recover a golden factor. -/

import D5.S1.Words.GoldenFactorComplexity
import Mathlib.Tactic

/-!
# Second-order recovery of consecutive golden factors

Rigo and Salimov, *Another generalization of abelian equivalence: Binomial
complexity of infinite words*, Theoretical Computer Science 601 (2015),
47-57, prove second-order binomial faithfulness for Sturmian factors.
This file proves the golden specialization from the repository's existing
Beatty window-count theorem. It is a formal integration of that classical
phenomenon, not a claim to have discovered the general theorem.

The proof has three steps. Intercept order makes all prefix counts comparable.
Equality of their sum forces equality of every prefix and hence every letter.
The prefix sum is recovered from the true-letter count and the number of
scattered true-false pairs by an exact integral identity.

The domain restriction matters: these are consecutive factors of one golden
word. Arbitrary prime-golden event lists need not satisfy this theorem. Neither
absolute occurrence positions nor prime labels are recovered.

Library search: `GoldenBalance` owns the Beatty count formula;
`GoldenFactorComplexity` owns `goldenFactor`. Their private prefix lemmas are
not exported. No existing public second-order factor recovery interface was
found in the repository search.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.GoldenFactorSecondOrderBinomialRigidity

open D5.S1.Words
open scoped BigOperators

/-- Sum of true counts in all prefixes, including the empty and full prefix. -/
def goldenPrefixArea (i n : Nat) : Nat :=
  ∑ m ∈ Finset.range (n + 1), goldenWindowTrueCount i m

/-- Number of scattered pairs whose earlier letter is true and later letter
is false. Each false letter contributes all preceding true letters. -/
def goldenTrueFalseCount (i n : Nat) : Nat :=
  ∑ k ∈ Finset.range n,
    if goldenWord (i + k) = true then 0 else goldenWindowTrueCount i k

/-- A reduced second-order binomial profile for a fixed factor length. -/
def goldenBinomialProfile (n i : Nat) : Nat × Nat :=
  (goldenWindowTrueCount i n, goldenTrueFalseCount i n)

private theorem floor_add_sub_floor (x t : Real) :
    ⌊x + t⌋ - ⌊x⌋ = ⌊Int.fract x + t⌋ := by
  have hx : (⌊x⌋ : Real) + (Int.fract x + t) = x + t := by
    calc
      (⌊x⌋ : Real) + (Int.fract x + t) =
          ((⌊x⌋ : Real) + Int.fract x) + t := by ring
      _ = x + t := by rw [Int.floor_add_fract]
  rw [← hx, Int.floor_intCast_add]
  omega

private theorem count_eq_floor_fract (i m : Nat) :
    (goldenWindowTrueCount i m : Int) =
      ⌊Int.fract (((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹) +
        (m : Real) * Real.goldenRatio⁻¹⌋ := by
  have hend : (((i + m + 1 : Nat) : Real) * Real.goldenRatio⁻¹) =
      (((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹) +
        (m : Real) * Real.goldenRatio⁻¹ := by
    push_cast
    ring
  rw [goldenWindowTrueCount_eq_floor, hend, floor_add_sub_floor]

private theorem count_mono_of_phase_le (i j : Nat)
    (hphase :
      Int.fract (((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹) ≤
        Int.fract (((j + 1 : Nat) : Real) * Real.goldenRatio⁻¹)) (m : Nat) :
    goldenWindowTrueCount i m ≤ goldenWindowTrueCount j m := by
  have h : (goldenWindowTrueCount i m : Int) ≤
      (goldenWindowTrueCount j m : Int) := by
    rw [count_eq_floor_fract, count_eq_floor_fract]
    apply Int.floor_mono
    linarith [hphase]
  exact_mod_cast h

/-- Any two golden starts have prefix-count vectors comparable in one common
orientation at every length. This is stronger than pointwise balance. -/
theorem golden_prefix_counts_comparable (i j : Nat) :
    (∀ m, goldenWindowTrueCount i m ≤ goldenWindowTrueCount j m) ∨
      (∀ m, goldenWindowTrueCount j m ≤ goldenWindowTrueCount i m) := by
  rcases le_total
      (Int.fract (((i + 1 : Nat) : Real) * Real.goldenRatio⁻¹))
      (Int.fract (((j + 1 : Nat) : Real) * Real.goldenRatio⁻¹)) with hij | hji
  · exact Or.inl (count_mono_of_phase_le i j hij)
  · exact Or.inr (count_mono_of_phase_le j i hji)

private theorem count_succ (i m : Nat) :
    goldenWindowTrueCount i (m + 1) = goldenWindowTrueCount i m +
      if goldenWord (i + m) = true then 1 else 0 := by
  classical
  by_cases h : goldenWord (i + m) = true <;>
    simp [goldenWindowTrueCount, Finset.range_add_one, Finset.filter_insert, h]

private theorem factor_eq_of_prefix_counts_eq (n i j : Nat)
    (hcounts : ∀ m ≤ n, goldenWindowTrueCount i m = goldenWindowTrueCount j m) :
    goldenFactor n i = goldenFactor n j := by
  unfold goldenFactor
  congr 1
  funext k
  have hbase := hcounts k k.isLt.le
  have hnext := hcounts (k + 1) (Nat.succ_le_of_lt k.isLt)
  rw [count_succ, count_succ] at hnext
  have hindicator : (if goldenWord (i + k) = true then 1 else 0) =
      if goldenWord (j + k) = true then 1 else 0 := by omega
  by_cases hi : goldenWord (i + k) = true <;>
    by_cases hj : goldenWord (j + k) = true <;> simp_all

/-- One prefix-area integer determines a consecutive golden factor when its
length is known. Occurrence positions themselves need not agree. -/
theorem golden_factor_eq_of_prefix_area_eq (n i j : Nat)
    (harea : goldenPrefixArea i n = goldenPrefixArea j n) :
    goldenFactor n i = goldenFactor n j := by
  change (∑ k ∈ Finset.range (n + 1), goldenWindowTrueCount i k) =
    (∑ k ∈ Finset.range (n + 1), goldenWindowTrueCount j k) at harea
  apply factor_eq_of_prefix_counts_eq n i j
  rcases golden_prefix_counts_comparable i j with hij | hji
  · intro m hm
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hij k)).mp harea
      m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  · intro m hm
    exact ((Finset.sum_eq_sum_iff_of_le (fun k _ => hji k)).mp harea.symm
      m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).symm

/-- The prefix area is determined by order-one and order-two binomial data:
`2 area = 2 #(true,false) + r(r+1)`, where `r` counts true letters. -/
theorem golden_prefix_area_binomial_identity (i n : Nat) :
    2 * goldenPrefixArea i n =
      2 * goldenTrueFalseCount i n +
        goldenWindowTrueCount i n * (goldenWindowTrueCount i n + 1) := by
  induction n with
  | zero =>
      simp [goldenPrefixArea, goldenTrueFalseCount, goldenWindowTrueCount]
  | succ n ih =>
      have harea : goldenPrefixArea i (n + 1) =
          goldenPrefixArea i n + goldenWindowTrueCount i (n + 1) := by
        unfold goldenPrefixArea
        rw [Finset.sum_range_succ]
      have hpairs : goldenTrueFalseCount i (n + 1) =
          goldenTrueFalseCount i n +
            if goldenWord (i + n) = true then 0 else goldenWindowTrueCount i n := by
        unfold goldenTrueFalseCount
        rw [Finset.sum_range_succ]
      rw [harea, hpairs, count_succ]
      by_cases hletter : goldenWord (i + n) = true
      · simp only [if_pos hletter]
        nlinarith [ih]
      · simp only [if_neg hletter]
        nlinarith [ih]

/-- Two reduced binomial statistics suffice to reconstruct any fixed-length
consecutive golden factor. -/
theorem golden_factor_eq_of_second_order_counts (n i j : Nat)
    (hones : goldenWindowTrueCount i n = goldenWindowTrueCount j n)
    (hpairs : goldenTrueFalseCount i n = goldenTrueFalseCount j n) :
    goldenFactor n i = goldenFactor n j := by
  apply golden_factor_eq_of_prefix_area_eq n i j
  have hi := golden_prefix_area_binomial_identity i n
  have hj := golden_prefix_area_binomial_identity j n
  rw [hones, hpairs] at hi
  omega

private theorem prefix_counts_eq_of_factor_eq (n i j : Nat)
    (hfactor : goldenFactor n i = goldenFactor n j) {m : Nat} (hm : m ≤ n) :
    goldenWindowTrueCount i m = goldenWindowTrueCount j m := by
  have hletters : (fun k : Fin n => goldenWord (i + k)) =
      fun k : Fin n => goldenWord (j + k) := List.ofFn_inj.mp hfactor
  unfold goldenWindowTrueCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hw⟩
    refine ⟨hk, ?_⟩
    rw [← congrFun hletters ⟨k, hk.trans_le hm⟩]
    exact hw
  · rintro ⟨hk, hw⟩
    refine ⟨hk, ?_⟩
    rw [congrFun hletters ⟨k, hk.trans_le hm⟩]
    exact hw

/-- On consecutive golden factors, the reduced second-order profile has
exactly the same fibers as the full word. -/
theorem golden_factor_eq_iff_second_order_profile_eq (n i j : Nat) :
    goldenFactor n i = goldenFactor n j ↔
      goldenBinomialProfile n i = goldenBinomialProfile n j := by
  constructor
  · intro hfactor
    apply Prod.ext
    · exact prefix_counts_eq_of_factor_eq n i j hfactor (le_refl n)
    · change goldenTrueFalseCount i n = goldenTrueFalseCount j n
      unfold goldenTrueFalseCount
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hletters : (fun t : Fin n => goldenWord (i + t)) =
          fun t : Fin n => goldenWord (j + t) := List.ofFn_inj.mp hfactor
      have hletter := congrFun hletters ⟨k, hkn⟩
      have hcount := prefix_counts_eq_of_factor_eq n i j hfactor hkn.le
      change goldenWord (i + k) = goldenWord (j + k) at hletter
      rw [hletter, hcount]
  · intro hprofile
    exact golden_factor_eq_of_second_order_counts n i j
      (congrArg Prod.fst hprofile) (congrArg Prod.snd hprofile)

/-- First-order counting alone really loses information on legal factors;
the scattered true-false count separates this smallest witness. -/
theorem legal_golden_first_order_collision :
    goldenWindowTrueCount 0 2 = goldenWindowTrueCount 1 2 ∧
      goldenFactor 2 0 ≠ goldenFactor 2 1 ∧
      goldenTrueFalseCount 0 2 = 1 ∧ goldenTrueFalseCount 1 2 = 0 := by
  decide

#print axioms golden_prefix_counts_comparable
#print axioms golden_factor_eq_of_prefix_area_eq
#print axioms golden_prefix_area_binomial_identity
#print axioms golden_factor_eq_of_second_order_counts
#print axioms golden_factor_eq_iff_second_order_profile_eq
#print axioms legal_golden_first_order_collision

end D5.S1.Words.GoldenFactorSecondOrderBinomialRigidity
