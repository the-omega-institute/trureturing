/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EightBitPhysicalLift
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal physical eight-bit insertion and its charge-prefix proof. -/
import D5.S3.Combinatorics.Circle.FourNegative.EightBitLiftBridge

/-! # Eight-seed physical four-gap family -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open D5.S3.Combinatorics.Circle.SparseNecklaceRounding
open scoped BigOperators

/-! The four-gap family used by the eight verified seeds. -/
def fourGaps (d : ℕ) : Fin 4 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => d

theorem fourGaps_period (d : ℕ) : period (fourGaps d) = d + 6 := by
  simp [period, gapList, fourGaps, Fin.sum_univ_succ]
  omega

theorem fourGaps_seed (d : ℕ) : necklaceSeed (fourGaps d) = 85 := by
  classical
  have hprefix (j : Fin 4) :
      (∑ q ∈ Finset.univ.filter (fun q : Fin 4 => q < j), fourGaps d q) =
        match j.val with
        | 0 => 0
        | 1 => 2
        | 2 => 4
        | 3 => 6
        | _ => 0 := by
    fin_cases j <;>
      simp only [Finset.sum_filter] <;>
      norm_num [fourGaps, Fin.sum_univ_succ]
  simp only [necklaceSeed, Fin.sum_univ_succ]
  rw [hprefix, hprefix, hprefix, hprefix]
  norm_num

private theorem fourGaps_legal (d : ℕ) (hd : 2 ≤ d) :
    ∀ j : Fin 4, 2 ≤ fourGaps d j := by
  intro j
  fin_cases j <;> simp [fourGaps] <;> omega

private theorem originalOrder_of_checks {k t : ℕ} (w : List (Fin k))
    (hp : w.Perm (List.finRange k))
    (hsum : (w.map (actualSource k t)).sum = 0)
    (hprefix : ∀ n : ℕ, n ≤ w.length →
      ((w.take n).map (actualSource k t)).sum ∈
        Set.Icc (0 : ℤ) (modulus k / 2)) :
    OriginalOrder k t w := by
  refine ⟨hp, hsum, ?_⟩
  intro n
  by_cases hn : n ≤ w.length
  · exact hprefix n hn
  · have ht : w.take n = w := List.take_of_length_le (by omega)
    rw [ht, hsum]
    have hm : 0 ≤ modulus k := by
      unfold modulus
      have : (1 : ℤ) ≤ 2 ^ k := by
        exact_mod_cast (Nat.one_le_two_pow (n := k))
      omega
    have hhalf : 0 ≤ modulus k / 2 := Int.ediv_nonneg hm (by norm_num)
    simp [Set.mem_Icc, hhalf]

private theorem seed_d2 :
    ∃ sigma : List (Fin 8), ∃ cut : ℕ, cut ≤ 8 ∧
      OriginalOrder 8 85 sigma ∧
      OriginalOrder 9 170 (earWord 8 sigma cut) := by
  let sigma : List (Fin 8) := [0,1,2,3,4,5,6,7]
  refine ⟨sigma, 1, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    · intro n hn
      have hn' : n ≤ 8 := by simpa [sigma] using hn
      interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 8 sigma 1)
    · decide
    · decide
    · intro n hn
      have hn' : n ≤ 9 := by simpa [sigma, earWord] using hn
      interval_cases n <;> decide

private theorem seed_d3 :
    ∃ sigma : List (Fin 9), ∃ cut : ℕ, cut ≤ 9 ∧
      OriginalOrder 9 85 sigma ∧
      OriginalOrder 10 170 (earWord 9 sigma cut) := by
  let sigma : List (Fin 9) := [0,1,2,3,4,5,6,7,8]
  refine ⟨sigma, 8, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 9 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 9 sigma 8)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 10 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d4 :
    ∃ sigma : List (Fin 10), ∃ cut : ℕ, cut ≤ 10 ∧
      OriginalOrder 10 85 sigma ∧
      OriginalOrder 11 170 (earWord 10 sigma cut) := by
  let sigma : List (Fin 10) := [0,2,3,4,5,6,7,1,8,9]
  refine ⟨sigma, 9, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 10 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 10 sigma 9)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 11 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d5 :
    ∃ sigma : List (Fin 11), ∃ cut : ℕ, cut ≤ 11 ∧
      OriginalOrder 11 85 sigma ∧
      OriginalOrder 12 170 (earWord 11 sigma cut) := by
  let sigma : List (Fin 11) := [0,1,3,4,5,6,7,8,2,9,10]
  refine ⟨sigma, 10, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 11 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 11 sigma 10)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 12 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d6 :
    ∃ sigma : List (Fin 12), ∃ cut : ℕ, cut ≤ 12 ∧
      OriginalOrder 12 85 sigma ∧
      OriginalOrder 13 170 (earWord 12 sigma cut) := by
  let sigma : List (Fin 12) := [0,1,2,4,5,6,7,8,9,3,10,11]
  refine ⟨sigma, 11, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 12 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 12 sigma 11)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 13 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d7 :
    ∃ sigma : List (Fin 13), ∃ cut : ℕ, cut ≤ 13 ∧
      OriginalOrder 13 85 sigma ∧
      OriginalOrder 14 170 (earWord 13 sigma cut) := by
  let sigma : List (Fin 13) := [0,1,2,3,5,6,7,8,9,10,4,11,12]
  refine ⟨sigma, 12, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 13 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 13 sigma 12)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 14 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d8 :
    ∃ sigma : List (Fin 14), ∃ cut : ℕ, cut ≤ 14 ∧
      OriginalOrder 14 85 sigma ∧
      OriginalOrder 15 170 (earWord 14 sigma cut) := by
  let sigma : List (Fin 14) := [0,1,2,3,4,6,7,8,9,10,11,5,12,13]
  refine ⟨sigma, 13, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 14 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 14 sigma 13)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 15 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

private theorem seed_d9 :
    ∃ sigma : List (Fin 15), ∃ cut : ℕ, cut ≤ 15 ∧
      OriginalOrder 15 85 sigma ∧
      OriginalOrder 16 170 (earWord 15 sigma cut) := by
  let sigma : List (Fin 15) := [0,1,2,3,4,5,7,8,9,10,11,12,6,13,14]
  refine ⟨sigma, 14, by decide, ?_, ?_⟩
  · apply originalOrder_of_checks sigma
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 15 := by simpa [sigma] using hn
    interval_cases n <;> decide
  · apply originalOrder_of_checks (earWord 15 sigma 14)
    · decide
    · decide
    intro n hn
    have hn' : n ≤ 16 := by simpa [sigma, earWord] using hn
    interval_cases n <;> decide

/-! The native p-minus-one theorem supplies the exact physical four-gap
rounding contract used by the corrected lift.  The remaining step from this
contract to a literal `OriginalOrder` joint word is kept separate so the
corner data cannot be mistaken for a completed lift. -/
theorem physical_rounding_family_contract (d : ℕ) (hd : 2 ≤ d) :
    PhysicalRounding (fourGaps d) := by
  exact uniform_sparse_necklace_rounding 4 (by decide : 1 ≤ 4)
    (fourGaps d) (fourGaps_legal d hd)

theorem fourGaps_eventual (d : ℕ) (hd : 9 ≤ d) :
    ∃ sigma : List (Fin (6 + d)), ∃ cut : ℕ, cut ≤ 6 + d ∧
      OriginalOrder (6 + d) 85 sigma ∧
      OriginalOrder (6 + d + 1) 170 (earWord (6 + d) sigma cut) := by
  exact actualSource_four_negative_eventual_joint_lift 2 2 2 d
    (by decide) (by decide) (by decide) hd

private theorem transport_pair {k l : ℕ} (hkl : k = l)
    (h : ∃ sigma : List (Fin k), ∃ cut : ℕ, cut ≤ k ∧
      OriginalOrder k 85 sigma ∧
      OriginalOrder (k + 1) 170 (earWord k sigma cut)) :
    ∃ sigma : List (Fin l), ∃ cut : ℕ, cut ≤ l ∧
      OriginalOrder l 85 sigma ∧
      OriginalOrder (l + 1) 170 (earWord l sigma cut) := by
  subst l
  exact h

theorem fourGaps_family :
    ∀ d : ℕ, 2 ≤ d →
      ∃ sigma : List (Fin (d + 6)), ∃ cut : ℕ, cut ≤ d + 6 ∧
        OriginalOrder (d + 6) 85 sigma ∧
        OriginalOrder (d + 7) 170 (earWord (d + 6) sigma cut) := by
  intro d hd
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases h10 : 10 ≤ d
    · obtain ⟨sigma, cut, hc, hold, hnew⟩ := ih (d - 8) (by omega) (by omega)
      obtain ⟨tau, c, hc', hfirst, hsecond, _⟩ :=
        insertion_only_eight_bit_lift (d - 8 + 6) (by omega) sigma cut hc hold hnew
      exact transport_pair (by omega) ⟨tau, c, hc', hfirst, hsecond⟩
    · have hd9 : d ≤ 9 := by omega
      interval_cases d <;>
        first
        | exact seed_d2
        | exact seed_d3
        | exact seed_d4
        | exact seed_d5
        | exact seed_d6
        | exact seed_d7
        | exact seed_d8
        | exact seed_d9

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
