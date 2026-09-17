/- GID: D5/S0/Certificates/GreathouseLogTwoFloorRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/GreathouseLogTwoFloorRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/GreathouseLogTwoFloorRefutation.claim; result=D5/S0/Certificates/GreathouseLogTwoFloorRefutation.result; claim=D5/S0/Certificates/GreathouseLogTwoFloorRefutation.claim
   digest: The index 1121626023352383 refutes Greathouse's floor formula for OEIS A175406. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.GreathouseLogTwoFloorRefutation

/-!
OEIS A175406 asks for the greatest natural number `k` such that
`(1 + 1 / n) ^ k <= 2`.  Charles R. Greathouse IV conjectured in 2012 that
this value is always `floor ((n + 1 / 2) * log 2)`.

The definition below is literal.  For positive `n` its defining set is
nonempty and bounded above.  As usual for the conditionally complete order
on the natural numbers, `sSup` is zero when its argument is unbounded.
-/

/-- The greatest exponent whose `n`-th harmonic perturbation stays at most two. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | (1 + 1 / (n : ℝ)) ^ k ≤ 2}

/-- Greathouse's conjectured closed formula for OEIS A175406. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n = ⌊((n : ℝ) + 1 / 2) * Real.log 2⌋₊

/-- The conjectured formula fails at `n = 1121626023352383`. -/
theorem result : ¬ claim := by
  let n₀ : ℕ := 1121626023352383
  let M : ℕ := 777451915729368
  let fTwo : ℕ → ℝ := fun k =>
    2 * (1 / (2 * k + 1)) * (1 / 3) ^ (2 * k + 1)
  let fWitness : ℕ → ℝ := fun k =>
    2 * (1 / (2 * k + 1)) * (1 / (2 * n₀ + 1)) ^ (2 * k + 1)
  let geometricTail : ℕ → ℝ := fun k =>
    (2 * (1 / 3 : ℝ) ^ 73) * (1 / 3) ^ k

  have hLogTwo : HasSum fTwo (Real.log 2) := by
    convert! Real.hasSum_log_one_add_inv (a := (1 : ℝ)) (by norm_num) using 1
    all_goals norm_num [fTwo]
  have hLogWitness :
      HasSum fWitness (Real.log (1 + 1 / (n₀ : ℝ))) := by
    convert! Real.hasSum_log_one_add_inv (a := (n₀ : ℝ)) (by norm_num [n₀]) using 1
    all_goals norm_num [fWitness]

  have hTwoLower :
      (∑ k ∈ Finset.range 36, fTwo k) ≤ Real.log 2 := by
    have hpartial := hLogTwo.summable.sum_le_tsum (Finset.range 36) (fun k _ => by
      dsimp [fTwo]
      positivity)
    rwa [hLogTwo.tsum_eq] at hpartial

  have hGeometric : HasSum geometricTail (1 / 3 ^ 72 : ℝ) := by
    convert! ((hasSum_geometric_of_lt_one
      (show (0 : ℝ) ≤ 1 / 3 by norm_num)
      (show (1 : ℝ) / 3 < 1 by norm_num)).mul_left
        (2 * (1 / 3 : ℝ) ^ 73)) using 1
    all_goals norm_num [geometricTail]
  have hTailPoint (k : ℕ) : fTwo (k + 36) ≤ geometricTail k := by
    have hfrac : (1 : ℝ) / (2 * ((k + 36 : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
      positivity
    have hpow :
        ((1 : ℝ) / 3) ^ (2 * (k + 36) + 1) ≤
          ((1 : ℝ) / 3) ^ (k + 73) := by
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    dsimp [fTwo, geometricTail]
    calc
      2 * (1 / (2 * ((k + 36 : ℕ) : ℝ) + 1)) * (1 / 3) ^ (2 * (k + 36) + 1) ≤
          2 * 1 * (1 / 3) ^ (2 * (k + 36) + 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfrac (by norm_num)) (by positivity)
      _ ≤ 2 * 1 * (1 / 3) ^ (k + 73) := by
        exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (2 * (1 / 3) ^ 73) * (1 / 3) ^ k := by
        rw [pow_add]
        ring
  have hTail : (∑' k : ℕ, fTwo (k + 36)) ≤ 1 / 3 ^ 72 := by
    have hshift : Summable (fun k : ℕ => fTwo (k + 36)) :=
      (summable_nat_add_iff 36).2 hLogTwo.summable
    exact (hshift.tsum_le_tsum hTailPoint hGeometric.summable).trans_eq hGeometric.tsum_eq
  have hTwoUpper :
      Real.log 2 ≤ (∑ k ∈ Finset.range 36, fTwo k) + 1 / 3 ^ 72 := by
    calc
      Real.log 2 = ∑' k : ℕ, fTwo k := hLogTwo.tsum_eq.symm
      _ = (∑ k ∈ Finset.range 36, fTwo k) + ∑' k : ℕ, fTwo (k + 36) :=
        (hLogTwo.summable.sum_add_tsum_nat_add 36).symm
      _ ≤ (∑ k ∈ Finset.range 36, fTwo k) + 1 / 3 ^ 72 :=
        add_le_add_right hTail _

  have hWitnessLower :
      (∑ k ∈ Finset.range 2, fWitness k) ≤
        Real.log (1 + 1 / (n₀ : ℝ)) := by
    have hpartial := hLogWitness.summable.sum_le_tsum (Finset.range 2) (fun k _ => by
      dsimp [fWitness]
      positivity)
    rwa [hLogWitness.tsum_eq] at hpartial

  have hExact :
      (M : ℝ) ≤ ((n₀ : ℝ) + 1 / 2) * (∑ k ∈ Finset.range 36, fTwo k) ∧
      ((n₀ : ℝ) + 1 / 2) *
          ((∑ k ∈ Finset.range 36, fTwo k) + 1 / 3 ^ 72) < (M : ℝ) + 1 ∧
      (∑ k ∈ Finset.range 36, fTwo k) + 1 / 3 ^ 72 <
        (M : ℝ) * (∑ k ∈ Finset.range 2, fWitness k) := by
    norm_num [n₀, M, fTwo, fWitness, Finset.sum_range_succ]
  have hPreviousExact :
      ((M - 1 : ℕ) : ℝ) * (1 / (n₀ : ℝ)) <
        ∑ k ∈ Finset.range 36, fTwo k := by
    norm_num [n₀, M, fTwo, Finset.sum_range_succ]

  have hFloor :
      ⌊((n₀ : ℝ) + 1 / 2) * Real.log 2⌋₊ = M := by
    apply (Nat.floor_eq_iff (by positivity)).2
    constructor
    · calc
        (M : ℝ) ≤ ((n₀ : ℝ) + 1 / 2) *
            (∑ k ∈ Finset.range 36, fTwo k) := hExact.1
        _ ≤ ((n₀ : ℝ) + 1 / 2) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hTwoLower (by positivity)
    · calc
        ((n₀ : ℝ) + 1 / 2) * Real.log 2 ≤
            ((n₀ : ℝ) + 1 / 2) *
              ((∑ k ∈ Finset.range 36, fTwo k) + 1 / 3 ^ 72) :=
          mul_le_mul_of_nonneg_left hTwoUpper (by positivity)
        _ < (M : ℝ) + 1 := hExact.2.1

  have hLogStrict :
      Real.log 2 < (M : ℝ) * Real.log (1 + 1 / (n₀ : ℝ)) := by
    calc
      Real.log 2 ≤ (∑ k ∈ Finset.range 36, fTwo k) + 1 / 3 ^ 72 := hTwoUpper
      _ < (M : ℝ) * (∑ k ∈ Finset.range 2, fWitness k) := hExact.2.2
      _ ≤ (M : ℝ) * Real.log (1 + 1 / (n₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left hWitnessLower (by positivity)

  have hBasePos : (0 : ℝ) < 1 + 1 / (n₀ : ℝ) := by positivity
  have hLogWitnessUpper :
      Real.log (1 + 1 / (n₀ : ℝ)) ≤ 1 / (n₀ : ℝ) := by
    calc
      Real.log (1 + 1 / (n₀ : ℝ)) ≤ (1 + 1 / (n₀ : ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos hBasePos
      _ = 1 / (n₀ : ℝ) := by ring
  have hPreviousLog :
      ((M - 1 : ℕ) : ℝ) * Real.log (1 + 1 / (n₀ : ℝ)) < Real.log 2 := by
    calc
      ((M - 1 : ℕ) : ℝ) * Real.log (1 + 1 / (n₀ : ℝ)) ≤
          ((M - 1 : ℕ) : ℝ) * (1 / (n₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left hLogWitnessUpper (by positivity)
      _ < ∑ k ∈ Finset.range 36, fTwo k := hPreviousExact
      _ ≤ Real.log 2 := hTwoLower
  have hPreviousPower :
      (1 + 1 / (n₀ : ℝ)) ^ (M - 1) ≤ 2 :=
    (Real.pow_le_iff_le_log hBasePos (by norm_num)).2 hPreviousLog.le
  have hPower : (2 : ℝ) < (1 + 1 / (n₀ : ℝ)) ^ M := by
    by_contra hnot
    have hle : (1 + 1 / (n₀ : ℝ)) ^ M ≤ (2 : ℝ) := le_of_not_gt hnot
    have hlogs := (Real.pow_le_iff_le_log hBasePos (by norm_num : (0 : ℝ) < 2)).1 hle
    exact (not_le_of_gt hLogStrict) hlogs

  have hSetNonempty :
      {k : ℕ | (1 + 1 / (n₀ : ℝ)) ^ k ≤ 2}.Nonempty := by
    refine ⟨0, ?_⟩
    norm_num
  have hEverySetMember (k : ℕ)
      (hk : k ∈ {j : ℕ | (1 + 1 / (n₀ : ℝ)) ^ j ≤ 2}) : k ≤ M - 1 := by
    have hklt : k < M := by
      by_contra hnot
      have hMk : M ≤ k := le_of_not_gt hnot
      have hBaseOne : (1 : ℝ) ≤ 1 + 1 / (n₀ : ℝ) :=
        le_add_of_nonneg_right (by positivity)
      have hMono :
          (1 + 1 / (n₀ : ℝ)) ^ M ≤ (1 + 1 / (n₀ : ℝ)) ^ k :=
        pow_le_pow_right₀ hBaseOne hMk
      exact (not_le_of_gt hPower) (hMono.trans hk)
    omega
  have hAUpper : a n₀ ≤ M - 1 := by
    unfold a
    exact csSup_le hSetNonempty hEverySetMember
  have hSetBounded : BddAbove {k : ℕ | (1 + 1 / (n₀ : ℝ)) ^ k ≤ 2} :=
    ⟨M - 1, hEverySetMember⟩
  have hALower : M - 1 ≤ a n₀ := by
    unfold a
    exact le_csSup hSetBounded hPreviousPower
  have hAExact : a n₀ = M - 1 := Nat.le_antisymm hAUpper hALower

  intro hClaim
  have hAtWitness := hClaim n₀ (by norm_num [n₀])
  rw [hFloor] at hAtWitness
  rw [hAExact] at hAtWitness
  have hlt : M - 1 < M := by norm_num [M]
  exact (Nat.ne_of_lt hlt) hAtWitness

#print axioms a
#print axioms claim
#print axioms result

end D5.S0.Certificates.GreathouseLogTwoFloorRefutation
