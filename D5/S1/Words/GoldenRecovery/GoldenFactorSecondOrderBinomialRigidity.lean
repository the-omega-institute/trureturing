/- GID: D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: True count and scattered true-false count recover a consecutive golden factor. -/

import D5.S1.Words.GoldenFactorComplexity
import D5.S1.Words.Mechanical.FloorFractShift
import D5.S1.Words.ReturnWords.GoldenWindowCounts
import Mathlib.Tactic

/-!
# Second-order recovery of consecutive golden factors

Rigo and Salimov, TCS 601 (2015),
47-57, DOI 10.1016/j.tcs.2015.07.025, established the general Sturmian result.
The proof below specializes it using the existing Beatty count owner.

Intercept order makes all prefix counts comparable. Equality of their sum
forces equality of each prefix and hence of each letter. The prefix sum is
recoverable from the true count and scattered true-false count.

The recovered state is a word, not its absolute occurrence position.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.GoldenRecovery.GoldenFactorSecondOrderBinomialRigidity

open D5.S1.Words
open scoped BigOperators

/-- Sum of the true counts of all prefixes, including the empty prefix. -/
def goldenPrefixArea (i n : Nat) : Nat :=
  ∑ m ∈ Finset.range (n + 1), goldenWindowTrueCount i m

/-- Scattered pairs with an earlier true and a later false letter. -/
def goldenTrueFalseCount (i n : Nat) : Nat :=
  ∑ k ∈ Finset.range n,
    if goldenWord (i + k) = true then 0 else goldenWindowTrueCount i k

/-- The reduced second-order profile at a fixed length. -/
def goldenBinomialProfile (n i : Nat) : Nat × Nat :=
  (goldenWindowTrueCount i n, goldenTrueFalseCount i n)

private theorem floor_add_sub_floor (x t : Real) :
    ⌊x + t⌋ - ⌊x⌋ = ⌊Int.fract x + t⌋ :=
  D5.S1.Words.Mechanical.FloorFractShift.floor_add_sub_floor x t

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

/-- All prefixes of two golden starts compare in one common orientation. -/
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
      if goldenWord (i + m) = true then 1 else 0 :=
  D5.S1.Words.ReturnWords.GoldenWindowCounts.window_count_succ goldenWord i m

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

/-- Prefix area determines a factor of known length, not its occurrence index. -/
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

/-- Exact integral area identity from first- and second-order binomial data. -/
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

/-- Reduced second-order statistics faithfully reconstruct a legal factor. -/
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
    goldenWindowTrueCount i m = goldenWindowTrueCount j m :=
  D5.S1.Words.ReturnWords.GoldenWindowCounts.window_counts_eq_of_factor_eq
    goldenWord hm hfactor

/-- The reduced profile and the full word induce the same kernel. -/
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

#print axioms golden_factor_eq_of_second_order_counts
#print axioms golden_factor_eq_iff_second_order_profile_eq

end D5.S1.Words.GoldenRecovery.GoldenFactorSecondOrderBinomialRigidity
