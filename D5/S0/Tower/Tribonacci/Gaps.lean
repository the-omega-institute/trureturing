/- GID: D5/S0/Tower/Tribonacci/Gaps
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Gaps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonically ordered Tribonacci name values have an exact three-gap spectrum. -/

import D5.S0.Tower.Tribonacci.Values

namespace D5.S0.Tower.Tribonacci.Gaps

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant

/-- The three possible adjacent lengths at level `Q`. -/
def IsTribonacciGap (Q : Nat) (gap : Real) : Prop :=
  gap = t ^ (-(Q : Int)) ∨
    gap = t ^ (-((Q + 1 : Nat) : Int)) ∨
      gap = t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))

/-- Multiplying by `t^-d` shifts every level-`Q` gap to level `Q+d`. -/
theorem isTribonacciGap_scale (d Q : Nat) (gap : Real) (hgap : IsTribonacciGap Q gap) :
    IsTribonacciGap (Q + d) (t ^ (-(d : Int)) * gap) := by
  rcases hgap with hlarge | hsmall | hcombined
  · left
    rw [hlarge, tribonacci_zpow_mul]
    congr 1
    push_cast
    omega
  · right
    left
    rw [hsmall, tribonacci_zpow_mul]
    congr 1
    push_cast
    omega
  · right
    right
    rw [hcombined, mul_add, tribonacci_zpow_mul, tribonacci_zpow_mul]
    apply congrArg₂ (· + ·)
    · congr 1
      push_cast
      omega
    · congr 1
      push_cast
      omega

theorem isTribonacciGap_scale_one (Q : Nat) (gap : Real) (hgap : IsTribonacciGap Q gap) :
    IsTribonacciGap (Q + 1) (t ^ (-1 : Int) * gap) := by
  have hcast : (1 : Int) = ((1 : Nat) : Int) := by norm_num
  rw [hcast]
  exact isTribonacciGap_scale 1 Q gap hgap

theorem isTribonacciGap_scale_two (Q : Nat) (gap : Real) (hgap : IsTribonacciGap Q gap) :
    IsTribonacciGap (Q + 2) (t ^ (-2 : Int) * gap) := by
  have hcast : (2 : Int) = ((2 : Nat) : Int) := by norm_num
  rw [hcast]
  exact isTribonacciGap_scale 2 Q gap hgap

theorem isTribonacciGap_scale_three (Q : Nat) (gap : Real)
    (hgap : IsTribonacciGap Q gap) :
    IsTribonacciGap (Q + 3) (t ^ (-3 : Int) * gap) := by
  have hcast : (3 : Int) = ((3 : Nat) : Int) := by norm_num
  rw [hcast]
  exact isTribonacciGap_scale 3 Q gap hgap

/-- The final index in the nonempty level-`Q` counting interval. -/
def tribonacciLastIndex (Q : Nat) : Fin (tribonacci (Q + 2)) :=
  ⟨tribonacci (Q + 2) - 1, Nat.sub_lt (tribonacci_level_pos Q) (by omega)⟩

/-- The distance from the final level-`Q` value to one. -/
noncomputable def tribonacciTerminalGap (Q : Nat) : Real :=
  1 - indexedNameValue Q (tribonacciLastIndex Q)

/-- The first name in every canonical level has value zero. -/
theorem indexedNameValue_zero (Q : Nat) :
    indexedNameValue Q ⟨0, tribonacci_level_pos Q⟩ = 0 := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hzero : Q = 0
      · subst Q
        convert indexedNameValue_level_zero using 1
      by_cases hone : Q = 1
      · subst Q
        convert indexedNameValue_level_one_zero using 1
      by_cases htwo : Q = 2
      · subst Q
        convert indexedNameValue_level_two_zero using 1
      obtain ⟨n, hn⟩ : ∃ n, Q = n + 3 := ⟨Q - 3, by omega⟩
      subst Q
      rw [indexedNameValue_lower n ⟨0, tribonacci_level_pos (n + 3)⟩
        (by have := tribonacci_level_pos (n + 2); omega)]
      have hindex :
          (⟨0, by have := tribonacci_level_pos (n + 2); omega⟩ :
              Fin (tribonacci (n + 4))) =
            ⟨0, tribonacci_level_pos (n + 2)⟩ := by
        apply Fin.ext
        simp
      rw [hindex, ih (n + 2) (by omega)]
      ring

/-- Adjacent and terminal gaps satisfy the same three-length invariant. -/
def TribonacciGapInvariant (Q : Nat) : Prop :=
  (∀ k (hk : k + 1 < tribonacci (Q + 2)),
      IsTribonacciGap Q
        (indexedNameValue Q ⟨k + 1, hk⟩ -
          indexedNameValue Q ⟨k, lt_trans (Nat.lt_succ_self k) hk⟩)) ∧
    IsTribonacciGap Q (tribonacciTerminalGap Q)

theorem tribonacciGapInvariant_zero : TribonacciGapInvariant 0 := by
  constructor
  · intro k hk
    norm_num [tribonacci] at hk
  · left
    have hlast : tribonacciLastIndex 0 = ⟨0, by decide⟩ := by
      apply Fin.ext
      norm_num [tribonacciLastIndex, tribonacci]
    rw [tribonacciTerminalGap, hlast, indexedNameValue_level_zero]
    norm_num

theorem tribonacciGapInvariant_one : TribonacciGapInvariant 1 := by
  constructor
  · intro k hk
    have hkzero : k = 0 := by
      norm_num [tribonacci] at hk
      omega
    subst k
    left
    rw [indexedNameValue_level_one_zero, indexedNameValue_level_one_one]
    ring
  · right
    right
    have hlast : tribonacciLastIndex 1 = ⟨1, by decide⟩ := by
      apply Fin.ext
      norm_num [tribonacciLastIndex, tribonacci]
    rw [tribonacciTerminalGap, hlast, indexedNameValue_level_one_one]
    change 1 - t ^ (-1 : Int) = t ^ (-2 : Int) + t ^ (-3 : Int)
    linarith [tribonacci_inverse_sum]

theorem tribonacciGapInvariant_two : TribonacciGapInvariant 2 := by
  constructor
  · intro k hk
    have hkbound : k ≤ 2 := by
      norm_num [tribonacci] at hk
      omega
    interval_cases k
    · left
      rw [indexedNameValue_level_two_zero, indexedNameValue_level_two_one]
      ring
    · right
      right
      rw [indexedNameValue_level_two_one, indexedNameValue_level_two_two]
      have hrec : t ^ (-1 : Int) =
          t ^ (-2 : Int) + t ^ (-3 : Int) + t ^ (-4 : Int) := by
        convert tribonacci_zpow_recurrence 1 using 1 <;> norm_num
      change t ^ (-1 : Int) - t ^ (-2 : Int) =
        t ^ (-3 : Int) + t ^ (-4 : Int)
      linarith
    · left
      rw [indexedNameValue_level_two_two, indexedNameValue_level_two_three]
      ring
  · right
    left
    have hlast : tribonacciLastIndex 2 = ⟨3, by decide⟩ := by
      apply Fin.ext
      norm_num [tribonacciLastIndex, tribonacci]
    rw [tribonacciTerminalGap, hlast, indexedNameValue_level_two_three]
    change 1 - (t ^ (-1 : Int) + t ^ (-2 : Int)) = t ^ (-3 : Int)
    linarith [tribonacci_inverse_sum]

theorem tribonacciGapInvariant_add_three (n : Nat)
    (hzero : TribonacciGapInvariant n)
    (hone : TribonacciGapInvariant (n + 1))
    (htwo : TribonacciGapInvariant (n + 2)) :
    TribonacciGapInvariant (n + 3) := by
  constructor
  · intro k hk
    change k + 1 < tribonacci (n + 5) at hk
    have htotal : tribonacci (n + 5) =
        tribonacci (n + 4) + (tribonacci (n + 3) + tribonacci (n + 2)) :=
      tribonacci_count_split n
    by_cases hfirst : k + 1 < tribonacci (n + 4)
    · have hkleft : k < tribonacci (n + 4) := lt_trans (Nat.lt_succ_self k) hfirst
      rw [indexedNameValue_lower n ⟨k + 1, by simpa using hk⟩ hfirst,
        indexedNameValue_lower n ⟨k, by simpa using
          (lt_trans (Nat.lt_succ_self k) hk)⟩ hkleft]
      have hfactor :
          t ^ (-1 : Int) * indexedNameValue (n + 2) ⟨k + 1, hfirst⟩ -
              t ^ (-1 : Int) * indexedNameValue (n + 2) ⟨k, hkleft⟩ =
            t ^ (-1 : Int) *
              (indexedNameValue (n + 2) ⟨k + 1, hfirst⟩ -
                indexedNameValue (n + 2) ⟨k, hkleft⟩) := by ring
      rw [hfactor]
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        isTribonacciGap_scale_one (n + 2) _ (htwo.1 k hfirst)
    · have hfirstLe : tribonacci (n + 4) ≤ k + 1 := Nat.le_of_not_gt hfirst
      by_cases hfirstEq : k + 1 = tribonacci (n + 4)
      · have hkleft : k < tribonacci (n + 4) := by omega
        have hsecondUpper : k + 1 < tribonacci (n + 4) + tribonacci (n + 3) := by
          have hpos : 0 < tribonacci (n + 3) := by
            simpa only [Nat.add_assoc, Nat.reduceAdd] using tribonacci_level_pos (n + 1)
          omega
        rw [indexedNameValue_lower n ⟨k, by simpa using
            (lt_trans (Nat.lt_succ_self k) hk)⟩ hkleft,
          indexedNameValue_middle n ⟨k + 1, by simpa using hk⟩ hfirstLe hsecondUpper]
        have hrightIndex :
            (⟨k + 1 - tribonacci (n + 4), by
                rw [show (n + 1) + 2 = n + 3 by omega]
                omega⟩ :
                Fin (tribonacci ((n + 1) + 2))) =
              ⟨0, tribonacci_level_pos (n + 1)⟩ := by
          apply Fin.ext
          simp [hfirstEq]
        rw [hrightIndex, indexedNameValue_zero]
        simp only [mul_zero, add_zero]
        have hlast :
            (⟨k, hkleft⟩ : Fin (tribonacci ((n + 2) + 2))) =
              tribonacciLastIndex (n + 2) := by
          apply Fin.ext
          change k = tribonacci (n + 4) - 1
          have := tribonacci_level_pos (n + 2)
          omega
        rw [hlast]
        have hfactor :
            t ^ (-1 : Int) -
                t ^ (-1 : Int) * indexedNameValue (n + 2)
                  (tribonacciLastIndex (n + 2)) =
              t ^ (-1 : Int) * tribonacciTerminalGap (n + 2) := by
          unfold tribonacciTerminalGap
          ring
        rw [hfactor]
        simpa only [Nat.add_assoc, Nat.reduceAdd] using
          isTribonacciGap_scale_one (n + 2) _ htwo.2
      · have hkSecond : tribonacci (n + 4) ≤ k := by omega
        by_cases hsecond : k + 1 < tribonacci (n + 4) + tribonacci (n + 3)
        · have hkSecondUpper : k < tribonacci (n + 4) + tribonacci (n + 3) := by omega
          rw [indexedNameValue_middle n ⟨k + 1, by simpa using hk⟩ hfirstLe hsecond,
            indexedNameValue_middle n ⟨k, by simpa using
              (lt_trans (Nat.lt_succ_self k) hk)⟩ hkSecond hkSecondUpper]
          have hresBound :
              (k - tribonacci (n + 4)) + 1 < tribonacci (n + 3) := by omega
          have hrightIndex :
              (⟨k + 1 - tribonacci (n + 4), by
                  rw [show (n + 1) + 2 = n + 3 by omega]
                  omega⟩ :
                  Fin (tribonacci ((n + 1) + 2))) =
                ⟨(k - tribonacci (n + 4)) + 1, hresBound⟩ := by
            apply Fin.ext
            change k + 1 - tribonacci (n + 4) =
              k - tribonacci (n + 4) + 1
            omega
          rw [hrightIndex]
          have hfactor :
              (t ^ (-1 : Int) + t ^ (-2 : Int) *
                  indexedNameValue (n + 1)
                    ⟨(k - tribonacci (n + 4)) + 1, hresBound⟩) -
                (t ^ (-1 : Int) + t ^ (-2 : Int) *
                  indexedNameValue (n + 1) ⟨k - tribonacci (n + 4), by
                    rw [show (n + 1) + 2 = n + 3 by omega]
                    omega⟩) =
                t ^ (-2 : Int) *
                  (indexedNameValue (n + 1)
                      ⟨(k - tribonacci (n + 4)) + 1, hresBound⟩ -
                    indexedNameValue (n + 1)
                      ⟨k - tribonacci (n + 4), by
                        rw [show (n + 1) + 2 = n + 3 by omega]
                        omega⟩) := by ring
          rw [hfactor]
          simpa only [Nat.add_assoc, Nat.reduceAdd] using
            isTribonacciGap_scale_two (n + 1) _
              (hone.1 (k - tribonacci (n + 4)) hresBound)
        · have hsecondLe :
              tribonacci (n + 4) + tribonacci (n + 3) ≤ k + 1 :=
            Nat.le_of_not_gt hsecond
          by_cases hsecondEq :
              k + 1 = tribonacci (n + 4) + tribonacci (n + 3)
          · have hkMiddle : k < tribonacci (n + 4) + tribonacci (n + 3) := by omega
            have hkUpper : k + 1 < tribonacci (n + 5) := by simpa using hk
            rw [indexedNameValue_middle n ⟨k, by simpa using
                (lt_trans (Nat.lt_succ_self k) hk)⟩ hkSecond hkMiddle,
              indexedNameValue_upper n ⟨k + 1, by simpa using hk⟩ hsecondLe]
            have hrightIndex :
                (⟨k + 1 - (tribonacci (n + 4) + tribonacci (n + 3)), by
                    rw [htotal] at hkUpper
                    omega⟩ : Fin (tribonacci (n + 2))) =
                  ⟨0, tribonacci_level_pos n⟩ := by
              apply Fin.ext
              simp [hsecondEq]
            rw [hrightIndex, indexedNameValue_zero]
            simp only [mul_zero, add_zero]
            have hleftIndex :
                (⟨k - tribonacci (n + 4), by
                    rw [show (n + 1) + 2 = n + 3 by omega]
                    omega⟩ :
                    Fin (tribonacci ((n + 1) + 2))) =
                  tribonacciLastIndex (n + 1) := by
              apply Fin.ext
              simp only [tribonacciLastIndex]
              rw [show (n + 1) + 2 = n + 3 by omega]
              have := tribonacci_level_pos (n + 1)
              omega
            rw [hleftIndex]
            have hfactor :
                (t ^ (-1 : Int) + t ^ (-2 : Int)) -
                    (t ^ (-1 : Int) + t ^ (-2 : Int) *
                      indexedNameValue (n + 1) (tribonacciLastIndex (n + 1))) =
                  t ^ (-2 : Int) * tribonacciTerminalGap (n + 1) := by
              unfold tribonacciTerminalGap
              ring
            rw [hfactor]
            simpa only [Nat.add_assoc, Nat.reduceAdd] using
              isTribonacciGap_scale_two (n + 1) _ hone.2
          · have hkUpper :
                tribonacci (n + 4) + tribonacci (n + 3) ≤ k := by omega
            rw [indexedNameValue_upper n ⟨k + 1, by simpa using hk⟩ hsecondLe,
              indexedNameValue_upper n ⟨k, by simpa using
                (lt_trans (Nat.lt_succ_self k) hk)⟩ hkUpper]
            have hresBound :
                (k - (tribonacci (n + 4) + tribonacci (n + 3))) + 1 <
                  tribonacci (n + 2) := by
              rw [htotal] at hk
              omega
            have hrightIndex :
                (⟨k + 1 - (tribonacci (n + 4) + tribonacci (n + 3)), by
                    rw [htotal] at hk
                    omega⟩ : Fin (tribonacci (n + 2))) =
                  ⟨(k - (tribonacci (n + 4) + tribonacci (n + 3))) + 1,
                    hresBound⟩ := by
              apply Fin.ext
              change k + 1 - (tribonacci (n + 4) + tribonacci (n + 3)) =
                k - (tribonacci (n + 4) + tribonacci (n + 3)) + 1
              omega
            rw [hrightIndex]
            have hfactor :
                (t ^ (-1 : Int) + t ^ (-2 : Int) + t ^ (-3 : Int) *
                    indexedNameValue n
                      ⟨(k - (tribonacci (n + 4) + tribonacci (n + 3))) + 1,
                        hresBound⟩) -
                  (t ^ (-1 : Int) + t ^ (-2 : Int) + t ^ (-3 : Int) *
                    indexedNameValue n
                      ⟨k - (tribonacci (n + 4) + tribonacci (n + 3)), by
                        rw [htotal] at hk
                        omega⟩) =
                  t ^ (-3 : Int) *
                    (indexedNameValue n
                        ⟨(k - (tribonacci (n + 4) + tribonacci (n + 3))) + 1,
                          hresBound⟩ -
                      indexedNameValue n
                        ⟨k - (tribonacci (n + 4) + tribonacci (n + 3)), by
                          rw [htotal] at hk
                          omega⟩) := by ring
            rw [hfactor]
            simpa only using
              isTribonacciGap_scale_three n _
                (hzero.1 (k - (tribonacci (n + 4) + tribonacci (n + 3))) hresBound)
  · have htotal : tribonacci (n + 5) =
        tribonacci (n + 4) + (tribonacci (n + 3) + tribonacci (n + 2)) :=
      tribonacci_count_split n
    have hlastUpper : tribonacci (n + 4) + tribonacci (n + 3) ≤
        (tribonacciLastIndex (n + 3)).1 := by
      simp only [tribonacciLastIndex]
      rw [htotal]
      have := tribonacci_level_pos n
      omega
    have hresBound :
        (tribonacciLastIndex (n + 3)).1 -
            (tribonacci (n + 4) + tribonacci (n + 3)) < tribonacci (n + 2) := by
      simp only [tribonacciLastIndex]
      rw [htotal]
      have := tribonacci_level_pos n
      omega
    have hresIndex :
        (⟨(tribonacciLastIndex (n + 3)).1 -
            (tribonacci (n + 4) + tribonacci (n + 3)), hresBound⟩ :
            Fin (tribonacci (n + 2))) = tribonacciLastIndex n := by
      apply Fin.ext
      simp only [tribonacciLastIndex]
      rw [htotal]
      have := tribonacci_level_pos n
      omega
    rw [tribonacciTerminalGap,
      indexedNameValue_upper n (tribonacciLastIndex (n + 3)) hlastUpper, hresIndex]
    have hfactor :
        1 - (t ^ (-1 : Int) + t ^ (-2 : Int) +
            t ^ (-3 : Int) * indexedNameValue n (tribonacciLastIndex n)) =
          t ^ (-3 : Int) * tribonacciTerminalGap n := by
      unfold tribonacciTerminalGap
      linarith [tribonacci_inverse_sum]
    rw [hfactor]
    simpa only using isTribonacciGap_scale_three n _ hzero.2

/-- Every level satisfies the joint adjacent/terminal three-gap invariant. -/
theorem tribonacci_gap_invariant (Q : Nat) : TribonacciGapInvariant Q := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hzero : Q = 0
      · simpa [hzero] using tribonacciGapInvariant_zero
      by_cases hone : Q = 1
      · simpa [hone] using tribonacciGapInvariant_one
      by_cases htwo : Q = 2
      · simpa [htwo] using tribonacciGapInvariant_two
      obtain ⟨n, hn⟩ : ∃ n, Q = n + 3 := ⟨Q - 3, by omega⟩
      subst Q
      exact tribonacciGapInvariant_add_three n
        (ih n (by omega)) (ih (n + 1) (by omega)) (ih (n + 2) (by omega))

/-- Consecutive canonical values have one of exactly three candidate lengths. -/
theorem consecutive_nameValue_gap (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) :
    IsTribonacciGap Q
      (indexedNameValue Q
          ⟨i.1 + 1, by have := i.2; have := tribonacci_level_pos Q; omega⟩ -
        indexedNameValue Q
          ⟨i.1, by have := i.2; have := tribonacci_level_pos Q; omega⟩) := by
  exact (tribonacci_gap_invariant Q).1 i.1 (by
    have := i.2
    have := tribonacci_level_pos Q
    omega)

/-- The frozen prefix equivalence enumerates name values in strictly increasing order. -/
theorem indexed_nameValue_strictMono (Q : Nat) : StrictMono (indexedNameValue Q) := by
  have hcard : tribonacci (Q + 2) - 1 + 1 = tribonacci (Q + 2) := by
    have := tribonacci_level_pos Q
    omega
  let values : Fin (tribonacci (Q + 2) - 1 + 1) → Real := fun i ↦
    indexedNameValue Q (Fin.cast hcard i)
  have hvalues : StrictMono values := Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    have hleft :
        Fin.cast hcard i.castSucc =
          (⟨i.1, by have := i.2; have := tribonacci_level_pos Q; omega⟩ :
            Fin (tribonacci (Q + 2))) := by
      apply Fin.ext
      simp
    have hright :
        Fin.cast hcard i.succ =
          (⟨i.1 + 1, by have := i.2; have := tribonacci_level_pos Q; omega⟩ :
            Fin (tribonacci (Q + 2))) := by
      apply Fin.ext
      simp
    rcases consecutive_nameValue_gap Q i with hlarge | hsmall | hcombined
    · have hpos : 0 < t ^ (-(Q : Int)) := zpow_pos tribonacciConstant_pos _
      dsimp [values]
      rw [hleft, hright]
      nlinarith
    · have hpos : 0 < t ^ (-((Q + 1 : Nat) : Int)) :=
        zpow_pos tribonacciConstant_pos _
      dsimp [values]
      rw [hleft, hright]
      nlinarith
    · have hposOne : 0 < t ^ (-((Q + 1 : Nat) : Int)) :=
        zpow_pos tribonacciConstant_pos _
      have hposTwo : 0 < t ^ (-((Q + 2 : Nat) : Int)) :=
        zpow_pos tribonacciConstant_pos _
      dsimp [values]
      rw [hleft, hright]
      nlinarith
  intro i j hij
  let i' : Fin (tribonacci (Q + 2) - 1 + 1) := Fin.cast hcard.symm i
  let j' : Fin (tribonacci (Q + 2) - 1 + 1) := Fin.cast hcard.symm j
  have hij' : i' < j' := hij
  simpa [values, i', j'] using hvalues hij'

/-- Distinct Tribonacci-admissible names have distinct real values. -/
theorem tribonacciNameValue_injective (Q : Nat) :
    Function.Injective (tribonacciNameValue Q) := by
  intro left right hvalue
  apply (tribonacciIndexEquiv Q).symm.injective
  apply (indexed_nameValue_strictMono Q).injective
  simpa [indexedNameValue] using hvalue

/-- All level-`Q` name values, listed increasingly. -/
noncomputable def sortedNameValues (Q : Nat) : List Real :=
  List.ofFn (indexedNameValue Q)

theorem sortedNameValues_sorted (Q : Nat) : (sortedNameValues Q).SortedLT := by
  unfold sortedNameValues
  exact (List.pairwise_ofFn.mpr (indexed_nameValue_strictMono Q)).sortedLT

theorem sortedNameValues_toFinset (Q : Nat) :
    (sortedNameValues Q).toFinset = Finset.univ.image (tribonacciNameValue Q) := by
  ext value
  simp only [List.mem_toFinset, sortedNameValues, List.mem_ofFn, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨tribonacciIndexEquiv Q i, by simpa [indexedNameValue] using hi⟩
  · rintro ⟨name, hname⟩
    refine ⟨(tribonacciIndexEquiv Q).symm name, ?_⟩
    simpa [indexedNameValue] using hname

/-- The difference at a specified adjacent index. -/
noncomputable def indexedGap (Q : Nat) (i : Fin (tribonacci (Q + 2) - 1)) : Real :=
  indexedNameValue Q
      ⟨i.1 + 1, by have := i.2; have := tribonacci_level_pos Q; omega⟩ -
    indexedNameValue Q
      ⟨i.1, by have := i.2; have := tribonacci_level_pos Q; omega⟩

/-- A gap length occurs when some adjacent index realizes it. -/
def GapOccurs (Q : Nat) (gap : Real) : Prop :=
  ∃ i : Fin (tribonacci (Q + 2) - 1), indexedGap Q i = gap

/-- Occurring gaps persist one level higher inside the zero-prefix block. -/
theorem gapOccurs_lower (n : Nat) (gap : Real) (hgap : GapOccurs (n + 2) gap) :
    GapOccurs (n + 3) (t ^ (-1 : Int) * gap) := by
  obtain ⟨i, hi⟩ := hgap
  have htotal : tribonacci (n + 5) =
      tribonacci (n + 4) + (tribonacci (n + 3) + tribonacci (n + 2)) :=
    tribonacci_count_split n
  have hibound : i.1 < tribonacci (n + 4) - 1 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using i.2
  have hnext : i.1 + 1 < tribonacci (n + 4) := by
    have hpos : 0 < tribonacci (n + 4) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using tribonacci_level_pos (n + 2)
    omega
  let j : Fin (tribonacci ((n + 3) + 2) - 1) := ⟨i.1, by
    change i.1 < tribonacci (n + 5) - 1
    rw [htotal]
    have hone := tribonacci_level_pos (n + 1)
    have hzero := tribonacci_level_pos n
    omega⟩
  have hjSuccTotal : j.1 + 1 < tribonacci (n + 5) := by
    dsimp [j]
    rw [htotal]
    omega
  have hjTotal : j.1 < tribonacci (n + 5) := lt_trans (Nat.lt_succ_self j.1) hjSuccTotal
  refine ⟨j, ?_⟩
  unfold indexedGap
  rw [indexedNameValue_lower n
      ⟨j.1 + 1, by simpa only [Nat.add_assoc, Nat.reduceAdd] using hjSuccTotal⟩
      (by simpa [j] using hnext),
    indexedNameValue_lower n
      ⟨j.1, by simpa only [Nat.add_assoc, Nat.reduceAdd] using hjTotal⟩
      (by have := hnext; simp [j]; omega)]
  have hright :
      (⟨j.1 + 1, by simpa [j] using hnext⟩ : Fin (tribonacci (n + 4))) =
        ⟨i.1 + 1, hnext⟩ := by
    apply Fin.ext
    simp [j]
  have hleft :
      (⟨j.1, by have := hnext; simp [j]; omega⟩ : Fin (tribonacci (n + 4))) =
        ⟨i.1, by omega⟩ := by
    apply Fin.ext
    simp [j]
  rw [hright, hleft, ← hi]
  unfold indexedGap
  ring

theorem tribonacci_zpow_shift_one (Q : Nat) :
    t ^ (-1 : Int) * t ^ (-(Q : Int)) = t ^ (-((Q + 1 : Nat) : Int)) := by
  rw [tribonacci_zpow_mul]
  congr 1
  push_cast
  omega

theorem combinedGap_shift_one (Q : Nat) :
    t ^ (-1 : Int) *
        (t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))) =
      t ^ (-((Q + 2 : Nat) : Int)) + t ^ (-((Q + 3 : Nat) : Int)) := by
  rw [mul_add, tribonacci_zpow_shift_one (Q + 1), tribonacci_zpow_shift_one (Q + 2)]

/-- At level three, all three lengths already occur. -/
theorem three_gaps_occur_at_three :
    GapOccurs 3 (t ^ (-3 : Int)) ∧
      GapOccurs 3 (t ^ (-4 : Int)) ∧
        GapOccurs 3 (t ^ (-4 : Int) + t ^ (-5 : Int)) := by
  have hrec1 : t ^ (-1 : Int) =
      t ^ (-2 : Int) + t ^ (-3 : Int) + t ^ (-4 : Int) := by
    convert tribonacci_zpow_recurrence 1 using 1 <;> norm_num
  have hrec2 : t ^ (-2 : Int) =
      t ^ (-3 : Int) + t ^ (-4 : Int) + t ^ (-5 : Int) := by
    convert tribonacci_zpow_recurrence 2 using 1 <;> norm_num
  constructor
  · refine ⟨⟨0, by decide⟩, ?_⟩
    unfold indexedGap
    rw [indexedNameValue_level_three_zero, indexedNameValue_level_three_one]
    ring
  · constructor
    · refine ⟨⟨3, by decide⟩, ?_⟩
      unfold indexedGap
      rw [indexedNameValue_level_three_three, indexedNameValue_level_three_four]
      linarith
    · refine ⟨⟨1, by decide⟩, ?_⟩
      unfold indexedGap
      rw [indexedNameValue_level_three_one, indexedNameValue_level_three_two]
      linarith

/-- From level three onward, every one of the three candidate lengths occurs. -/
theorem three_gaps_occur (Q : Nat) (hQ : 3 ≤ Q) :
    GapOccurs Q (t ^ (-(Q : Int))) ∧
      GapOccurs Q (t ^ (-((Q + 1 : Nat) : Int))) ∧
        GapOccurs Q
          (t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))) := by
  obtain ⟨n, hn⟩ : ∃ n, Q = n + 3 := ⟨Q - 3, by omega⟩
  subst Q
  induction n with
  | zero => simpa using three_gaps_occur_at_three
  | succ n ih =>
      rcases ih (by omega) with ⟨hlarge, hsmall, hcombined⟩
      have hlarge' := gapOccurs_lower (n + 1) _ hlarge
      have hsmall' := gapOccurs_lower (n + 1) _ hsmall
      have hcombined' := gapOccurs_lower (n + 1) _ hcombined
      constructor
      · rw [tribonacci_zpow_shift_one] at hlarge'
        simpa only [Nat.add_assoc, Nat.reduceAdd] using hlarge'
      · constructor
        · rw [tribonacci_zpow_shift_one] at hsmall'
          simpa only [Nat.add_assoc, Nat.reduceAdd] using hsmall'
        · rw [combinedGap_shift_one] at hcombined'
          simpa only [Nat.add_assoc, Nat.reduceAdd] using hcombined'

/-- The finite set of differences between consecutive sorted name values. -/
noncomputable def adjacentGapSpectrum (Q : Nat) : Finset Real :=
  Finset.univ.image (indexedGap Q)

/-- From level three onward, the adjacent spectrum is exactly the three stated lengths. -/
theorem adjacent_gap_spectrum (Q : Nat) (hQ : 3 ≤ Q) :
    adjacentGapSpectrum Q =
      {t ^ (-(Q : Int)), t ^ (-((Q + 1 : Nat) : Int)),
        t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))} := by
  ext gap
  constructor
  · intro hgap
    rw [adjacentGapSpectrum, Finset.mem_image] at hgap
    obtain ⟨i, _, hi⟩ := hgap
    subst gap
    rcases consecutive_nameValue_gap Q i with hlarge | hsmall | hcombined
    · simp [indexedGap, hlarge]
    · simp [indexedGap, hsmall]
    · simp [indexedGap, hcombined]
  · intro hgap
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgap
    rcases three_gaps_occur Q hQ with ⟨hlarge, hsmall, hcombined⟩
    rcases hgap with hgap | hgap | hgap
    · rw [hgap, adjacentGapSpectrum, Finset.mem_image]
      obtain ⟨i, hi⟩ := hlarge
      exact ⟨i, Finset.mem_univ _, hi⟩
    · rw [hgap, adjacentGapSpectrum, Finset.mem_image]
      obtain ⟨i, hi⟩ := hsmall
      exact ⟨i, Finset.mem_univ _, hi⟩
    · rw [hgap, adjacentGapSpectrum, Finset.mem_image]
      obtain ⟨i, hi⟩ := hcombined
      exact ⟨i, Finset.mem_univ _, hi⟩

/-- The middle length lies strictly between the short and long lengths. -/
theorem tribonacci_gap_lengths_order (Q : Nat) :
    t ^ (-((Q + 1 : Nat) : Int)) <
        t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) ∧
      t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) <
        t ^ (-(Q : Int)) := by
  have hposTwo : 0 < t ^ (-((Q + 2 : Nat) : Int)) :=
    zpow_pos tribonacciConstant_pos _
  have hposThree : 0 < t ^ (-((Q + 3 : Nat) : Int)) :=
    zpow_pos tribonacciConstant_pos _
  constructor
  · linarith
  · linarith [tribonacci_zpow_recurrence Q]

/-- Thus the exact adjacent-gap spectrum has cardinality three. -/
theorem adjacent_gap_spectrum_card (Q : Nat) (hQ : 3 ≤ Q) :
    (adjacentGapSpectrum Q).card = 3 := by
  rw [adjacent_gap_spectrum Q hQ]
  rcases tribonacci_gap_lengths_order Q with ⟨hshort, hlong⟩
  have hlargeSmall : t ^ (-(Q : Int)) ≠ t ^ (-((Q + 1 : Nat) : Int)) := by
    linarith
  have hlargeCombined : t ^ (-(Q : Int)) ≠
      t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) := by
    linarith
  have hsmallCombined : t ^ (-((Q + 1 : Nat) : Int)) ≠
      t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) := by
    linarith
  have hlargeNotMem : t ^ (-(Q : Int)) ∉
      ({t ^ (-((Q + 1 : Nat) : Int)),
        t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))} :
          Finset Real) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hlargeSmall, hlargeCombined⟩
  have hsmallNotMem : t ^ (-((Q + 1 : Nat) : Int)) ∉
      ({t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))} :
        Finset Real) := by
    simpa only [Finset.mem_singleton] using hsmallCombined
  rw [Finset.card_insert_of_notMem hlargeNotMem,
    Finset.card_insert_of_notMem hsmallNotMem, Finset.card_singleton]

end D5.S0.Tower.Tribonacci.Gaps
