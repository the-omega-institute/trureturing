/- GID: D5/S3/Combinatorics/PopStack/PopStackMaximumInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMaximumInsertion
   mirror-E: none(waiver:maximum-second-parity-insertion)
   anchors: []
   utility: none
   digest: Parity insertion before the minimum preserves the augmented maximum-second family. -/

import D5.S3.Combinatorics.PopStack.PopStackMaximumTerminal
import D5.S3.Combinatorics.PopStack.PopStackMaximumIntervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMaximumInsertion

open PopStackDefs PopStackParallel PopStackExtra PopStackMaximumPrefix
open PopStackMaximumTerminal PopStackMaximumIntervals

theorem maximum_second_insertion (permutation : List ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hlength : 4 ≤ permutation.length) (hmaximum : permutation.getD 1 0 = permutation.length)
    (hupper : ∀ first second, 2 ≤ first → first < second → second < permutation.length →
      permutation.getD 0 0 < permutation.getD first 0 →
      permutation.getD 0 0 < permutation.getD second 0 →
      permutation.getD second 0 < permutation.getD first 0)
    (hlower : ∀ first smaller larger, 2 ≤ first → first < smaller → first < larger →
      smaller < permutation.length → larger < permutation.length →
      permutation.getD first 0 < permutation.getD 0 0 →
      permutation.getD smaller 0 < permutation.getD 0 0 →
      permutation.getD larger 0 < permutation.getD 0 0 →
      ¬ (permutation.getD smaller 0 < permutation.getD first 0 ∧
        permutation.getD first 0 < permutation.getD larger 0))
    (hbonds : ∀ index, index + 1 < permutation.length →
      permutation.getD index 0 ≠ permutation.getD (index + 1) 0 + 1 ∧
      permutation.getD (index + 1) 0 ≠ permutation.getD index 0 + 1)
    (minimumIndex : ℕ) (hminimumLater : 2 ≤ minimumIndex)
    (hminimumBound : minimumIndex < permutation.length)
    (hminimum : permutation.getD minimumIndex 0 = 1)
    (hnotP : permutation ≠ P (permutation.length / 2))
    (hnotE : permutation ≠ E (permutation.length / 2)) :
    let rank := if minimumIndex % 2 = 0 then
      permutation.getD 0 0 - minimumIndex / 2 + 1
      else permutation.length - (minimumIndex - 1) / 2 + 1
    let shift := fun entry => if rank ≤ entry then entry + 1 else entry
    let member := (permutation.map shift).insertIdx minimumIndex rank
    member.Perm (List.range' 1 member.length) ∧ member.getD 1 0 = member.length ∧
      member.getD (minimumIndex + 1) 0 = 1 ∧ InC member ∧
      IsSimple member ∧ member ≠ P (member.length / 2) ∧ member ≠ E (member.length / 2) ∧
      (member.eraseIdx minimumIndex).map
        (fun entry => if rank < entry then entry - 1 else entry) = permutation := by
  classical
  let value := fun index => permutation.getD index 0
  let alpha := value 0
  let half := minimumIndex / 2
  let rank := if minimumIndex % 2 = 0 then alpha - half + 1
    else permutation.length - (minimumIndex - 1) / 2 + 1
  let shift := fun entry => if rank ≤ entry then entry + 1 else entry
  let member := (permutation.map shift).insertIdx minimumIndex rank
  let newValue := fun index => member.getD index 0
  let oldIndex := fun index => if index < minimumIndex then index else index - 1
  change member.Perm (List.range' 1 member.length) ∧ newValue 1 = member.length ∧
    newValue (minimumIndex + 1) = 1 ∧ InC member ∧
    IsSimple member ∧ member ≠ P (member.length / 2) ∧ member ≠ E (member.length / 2) ∧
    (member.eraseIdx minimumIndex).map
      (fun entry => if rank < entry then entry - 1 else entry) = permutation
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hdistinct : ∀ first second, first < permutation.length →
      second < permutation.length → value first = value second → first = second := by
    intro first second hfirst hsecond heq
    exact (List.getD_inj hfirst hsecond hnodup).mp heq
  have hbounds : ∀ index, index < permutation.length →
      1 ≤ value index ∧ value index ≤ permutation.length := by
    intro index hindex
    have hmem : value index ∈ permutation := by
      rw [show value index = permutation[index] from List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  have halphaBounds := hbounds 0 (by omega)
  have halphaNotMinimum : alpha ≠ 1 := by
    intro heq
    have hh := hdistinct 0 minimumIndex (by omega) hminimumBound
      (by change alpha = permutation.getD minimumIndex 0; rw [hminimum]; exact heq)
    omega
  have halphaNotMaximum : alpha ≠ permutation.length := by
    intro heq
    have hh := hdistinct 0 1 (by omega) (by omega)
      (by change alpha = permutation.getD 1 0; rw [hmaximum]; exact heq)
    omega
  have halpha : 2 ≤ alpha ∧ alpha < permutation.length := by omega
  have hprefix := maximum_second_prefix permutation hperm hlength hmaximum hupper hlower
    hbonds minimumIndex hminimumBound hminimum
  have hprefixValue : ∀ index, index < minimumIndex → value index =
      if index % 2 = 0 then alpha - index / 2 else permutation.length - index / 2 := hprefix
  have hupperRoom : alpha + half ≤ permutation.length := by
    by_contra hnot
    have hposition : 2 * (permutation.length - alpha) + 1 < minimumIndex := by
      dsimp [half] at *; omega
    have heq : value (2 * (permutation.length - alpha) + 1) = value 0 := by
      have hodd : (2 * (permutation.length - alpha) + 1) % 2 ≠ 0 := by omega
      have hquotient : (2 * (permutation.length - alpha) + 1) / 2 =
          permutation.length - alpha := by omega
      rw [hprefixValue _ hposition, if_neg hodd, hquotient]
      change permutation.length - (permutation.length - alpha) = alpha
      omega
    have hh := hdistinct _ 0 (by omega) (by omega) heq
    omega
  have hprefixSide : ∀ index, index < minimumIndex →
      (alpha < value index ↔ index % 2 = 1) ∧
      (value index < alpha ↔ 0 < index ∧ index % 2 = 0) := by
    intro index hindex
    have hprefixEntry := hprefixValue index hindex
    dsimp [half] at hupperRoom
    split_ifs at hprefixEntry <;> constructor <;> omega
  have hlowerRoom :
      if minimumIndex % 2 = 0 then half + 1 ≤ alpha else half + 2 ≤ alpha := by
    let lastLower := if minimumIndex % 2 = 0 then minimumIndex - 2 else minimumIndex - 1
    have hlast : lastLower < minimumIndex := by dsimp [lastLower]; split_ifs <;> omega
    have hentry := hprefixValue lastLower hlast
    have hbound := hbounds lastLower (by omega)
    have hne : value lastLower ≠ 1 := by
      intro heq
      have hh := hdistinct lastLower minimumIndex (by omega) hminimumBound
        (by change value lastLower = permutation.getD minimumIndex 0; rw [hminimum]; exact heq)
      omega
    dsimp only [lastLower, value, alpha, half] at hentry hbound hne ⊢
    split_ifs at hentry hbound hne ⊢ <;> omega
  have hrankSide :
      if minimumIndex % 2 = 0 then 2 ≤ rank ∧ rank ≤ alpha
      else alpha < rank ∧ rank ≤ permutation.length := by
    dsimp [rank, half] at *
    split_ifs at hlowerRoom ⊢ <;> omega
  have hrank : 3 ≤ rank ∧ rank ≤ permutation.length := by
    by_cases heven : minimumIndex % 2 = 0
    · have hrankEq : rank = alpha - half + 1 := by simp only [rank, heven, if_true]
      rw [if_pos heven] at hrankSide hlowerRoom
      have hnotTwo : rank ≠ 2 := by
        intro heq
        have hexhausted : permutation.getD 0 0 = minimumIndex / 2 + 1 := by
          change alpha = minimumIndex / 2 + 1
          dsimp [half] at *; omega
        obtain ⟨hterminal, hE⟩ | ⟨hterminal, hP⟩ := exhausted_lower_prefix permutation hperm
          hlength hmaximum hupper hlower hbonds minimumIndex hminimumLater hminimumBound
          hminimum heven hexhausted
        · have hhalfEq : permutation.length / 2 = minimumIndex / 2 := by omega
          exact hnotE (by simpa only [hhalfEq] using hE)
        · have hhalfEq : permutation.length / 2 = minimumIndex / 2 + 1 := by omega
          exact hnotP (by simpa only [hhalfEq] using hP)
      omega
    · rw [if_neg heven] at hrankSide
      omega
  have hbeforeRank : ∀ index, index < minimumIndex →
      (if minimumIndex % 2 = 0 then value index < alpha else alpha < value index) →
      rank ≤ value index := by
    intro index hindex hside
    have hentry := hprefixValue index hindex
    have hsides := hprefixSide index hindex
    dsimp only [rank, half, value, alpha] at hentry hsides hside hlowerRoom hupperRoom halpha ⊢
    split_ifs at hentry hside hlowerRoom ⊢ <;> omega
  have hafterRank : ∀ index, minimumIndex ≤ index → index < permutation.length →
      (if minimumIndex % 2 = 0 then value index < alpha else alpha < value index) →
      value index < rank := by
    intro index hafter hindex hside
    by_contra hnot
    have hbound := hbounds index hindex
    by_cases heven : minimumIndex % 2 = 0
    · rw [if_pos heven] at hside
      have hrankEq : rank = alpha - half + 1 := by simp only [rank, heven, if_true]
      have hposition : 2 * (alpha - value index) < minimumIndex := by
        dsimp [half] at *; omega
      have heq : value (2 * (alpha - value index)) = value index := by
        rw [hprefixValue _ hposition]
        split_ifs <;> omega
      have hh := hdistinct _ index (by omega) hindex heq
      omega
    · rw [if_neg heven] at hside
      have hrankEq : rank = permutation.length - (minimumIndex - 1) / 2 + 1 := by
        simp only [rank, heven, if_false]
      have hposition : 2 * (permutation.length - value index) + 1 < minimumIndex := by omega
      have heq : value (2 * (permutation.length - value index) + 1) = value index := by
        rw [hprefixValue _ hposition]
        split_ifs <;> omega
      have hh := hdistinct _ index (by omega) hindex heq
      omega
  have hlowerBefore : ∀ first second, first < minimumIndex → first < second →
      second < permutation.length → value first < alpha → value second < alpha →
      value second < value first := by
    intro first second hfirst horder hsecond hfirstLow hsecondLow
    have hsides := hprefixSide first hfirst
    have hfirstEntry := hprefixValue first hfirst
    have hfirstBounds := hbounds first (by omega)
    have hsecondBounds := hbounds second hsecond
    by_cases hbefore : second < minimumIndex
    · have hsecondSide := hprefixSide second hbefore
      have hsecondEntry := hprefixValue second hbefore
      split_ifs at hfirstEntry hsecondEntry <;> omega
    by_contra hnot
    have hbound := hbounds second hsecond
    have hposition : 2 * (alpha - value second) ≤ first := by
      split_ifs at hfirstEntry <;> omega
    have heq : value (2 * (alpha - value second)) = value second := by
      rw [hprefixValue _ (by omega)]
      split_ifs <;> omega
    have hh := hdistinct _ second (by omega) hsecond heq
    omega
  have hshiftOrder : ∀ first second, shift first < shift second ↔ first < second := by
    intro first second
    dsimp [shift]
    split_ifs <;> omega
  have hshiftInjective : Function.Injective shift := by
    intro first second heq
    dsimp [shift] at heq
    split_ifs at heq <;> omega
  have hshiftNoRank : ∀ entry, shift entry ≠ rank := by
    intro entry
    dsimp [shift]
    split_ifs <;> omega
  have hmemberLength : member.length = permutation.length + 1 := by
    simp [member, List.length_insertIdx, hminimumBound.le]
  have hgetBefore : ∀ index, index < minimumIndex → newValue index = shift (value index) := by
    intro index hindex
    change member.getD index 0 = _
    rw [List.getD_eq_getElem _ _ (by omega)]
    change ((permutation.map shift).insertIdx minimumIndex rank)[index] = _
    rw [List.getElem_insertIdx_of_lt hindex, List.getElem_map]
    change shift permutation[index] = shift (permutation.getD index 0)
    rw [List.getD_eq_getElem _ _ (by omega)]
  have hgetAt : newValue minimumIndex = rank := by
    change member.getD minimumIndex 0 = _
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_insertIdx_self _
  have hgetAfter : ∀ index, minimumIndex < index → index < member.length →
      newValue index = shift (value (index - 1)) := by
    intro index hafter hindex
    change member.getD index 0 = _
    rw [List.getD_eq_getElem _ _ hindex]
    change ((permutation.map shift).insertIdx minimumIndex rank)[index] = _
    rw [List.getElem_insertIdx_of_gt hafter, List.getElem_map]
    change shift permutation[index - 1] = shift (permutation.getD (index - 1) 0)
    rw [List.getD_eq_getElem _ _ (by omega)]
  have hgetOld : ∀ index, index < member.length → index ≠ minimumIndex →
      newValue index = shift (value (oldIndex index)) := by
    intro index hindex hne
    dsimp only [oldIndex]
    split_ifs with hbefore
    · exact hgetBefore index hbefore
    · exact hgetAfter index (by omega) hindex
  have holdBounds : ∀ index, index < member.length → index ≠ minimumIndex →
      oldIndex index < permutation.length := by
    intro index hindex hne
    dsimp [oldIndex]; split_ifs <;> omega
  have holdOrder : ∀ first second, first < second → first ≠ minimumIndex →
      second ≠ minimumIndex → oldIndex first < oldIndex second := by
    intro first second horder hfirst hsecond
    dsimp [oldIndex]; split_ifs <;> omega
  have holdPositive : ∀ index, 2 ≤ index → index ≠ minimumIndex →
      2 ≤ oldIndex index := by
    intro index hindex hne
    dsimp [oldIndex]; split_ifs <;> omega
  have hnewAlpha : newValue 0 = shift alpha := hgetBefore 0 (by omega)
  have hnewSide :
      if minimumIndex % 2 = 0 then rank < newValue 0 else newValue 0 < rank := by
    rw [hnewAlpha]
    dsimp [shift]
    split_ifs at hrankSide ⊢ <;> omega
  have hmemberNodup : member.Nodup := by
    have hcons : (rank :: permutation.map shift).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, hnodup.map hshiftInjective⟩
      intro hmem
      obtain ⟨entry, _, heq⟩ := List.mem_map.mp hmem
      exact hshiftNoRank entry heq
    exact (List.perm_insertIdx rank (permutation.map shift)
      (by simpa using hminimumBound.le)).nodup_iff.mpr hcons
  have hmemberPerm : member.Perm (List.range' 1 member.length) := by
    apply (List.perm_ext_iff_of_nodup hmemberNodup (List.nodup_range' _)).mpr
    intro entry
    rw [List.mem_range'_1, hmemberLength]
    change entry ∈ (permutation.map shift).insertIdx minimumIndex rank ↔ _
    rw [List.mem_insertIdx (by simpa using hminimumBound.le)]
    constructor
    · rintro (rfl | hmem)
      · omega
      · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hmem
        have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hold)
        dsimp [shift]; split_ifs <;> omega
    · rintro ⟨hpositive, hbound⟩
      by_cases heq : entry = rank
      · exact Or.inl heq
      refine Or.inr ?_
      by_cases hbelow : entry < rank
      · refine List.mem_map.mpr ⟨entry, hperm.mem_iff.mpr (List.mem_range'_1.mpr ?_), ?_⟩
        · omega
        · dsimp [shift]; split_ifs <;> omega
      · refine List.mem_map.mpr ⟨entry - 1,
          hperm.mem_iff.mpr (List.mem_range'_1.mpr ?_), ?_⟩
        · omega
        · dsimp [shift]; split_ifs <;> omega
  have hmemberMaximum : newValue 1 = member.length := by
    rw [hgetBefore 1 (by omega)]
    change shift (permutation.getD 1 0) = member.length
    rw [hmaximum, hmemberLength]
    dsimp [shift]; split_ifs <;> omega
  have hmemberMinimum : newValue (minimumIndex + 1) = 1 := by
    rw [hgetAfter _ (by omega) (by omega)]
    simp only [Nat.add_sub_cancel, value, hminimum]
    dsimp [shift]; split_ifs <;> omega
  have hmemberUpper : ∀ first second, 2 ≤ first → first < second →
      second < member.length →
      newValue 0 < newValue first → newValue 0 < newValue second →
      newValue second < newValue first := by
    intro first second hfirst horder hsecond hfirstHigh hsecondHigh
    by_cases hfirstNew : first = minimumIndex
    · subst first
      rw [hgetAt] at hfirstHigh ⊢
      have hne : second ≠ minimumIndex := by omega
      rw [hgetOld second hsecond hne] at hsecondHigh ⊢
      rw [hnewAlpha, hshiftOrder] at hsecondHigh
      by_cases heven : minimumIndex % 2 = 0
      · rw [if_pos heven] at hnewSide
        omega
      · have htail := hafterRank (oldIndex second)
          (by dsimp [oldIndex]; split_ifs <;> omega) (holdBounds second hsecond hne)
          (by simpa only [if_neg heven] using hsecondHigh)
        dsimp [shift]; split_ifs <;> omega
    by_cases hsecondNew : second = minimumIndex
    · subst second
      rw [hgetAt] at hsecondHigh ⊢
      rw [hgetBefore first (by omega)] at hfirstHigh ⊢
      rw [hnewAlpha, hshiftOrder] at hfirstHigh
      by_cases heven : minimumIndex % 2 = 0
      · rw [if_pos heven] at hnewSide
        omega
      · have hbefore := hbeforeRank first (by omega)
          (by simpa only [if_neg heven] using hfirstHigh)
        dsimp [shift]; split_ifs; omega
    rw [hgetOld first (by omega) hfirstNew] at hfirstHigh ⊢
    rw [hgetOld second hsecond hsecondNew] at hsecondHigh ⊢
    rw [hnewAlpha, hshiftOrder] at hfirstHigh hsecondHigh
    rw [hshiftOrder]
    exact hupper (oldIndex first) (oldIndex second) (holdPositive first hfirst hfirstNew)
      (holdOrder first second horder hfirstNew hsecondNew)
      (holdBounds second hsecond hsecondNew) hfirstHigh hsecondHigh
  have hmemberLower : ∀ first smaller larger, 2 ≤ first → first < smaller →
      first < larger →
      smaller < member.length → larger < member.length → newValue first < newValue 0 →
      newValue smaller < newValue 0 → newValue larger < newValue 0 →
      ¬ (newValue smaller < newValue first ∧ newValue first < newValue larger) := by
    intro first smaller larger hfirst hsmaller hlarger hsmallerBound hlargerBound
      hfirstLow hsmallerLow hlargerLow hstraddle
    by_cases hfirstNew : first = minimumIndex
    · subst first
      rw [hgetAt] at hfirstLow hstraddle
      have hlargerNe : larger ≠ minimumIndex := by omega
      rw [hgetAfter larger (by omega) hlargerBound] at hlargerLow hstraddle
      rw [hnewAlpha, hshiftOrder] at hlargerLow
      by_cases heven : minimumIndex % 2 = 0
      · have htail := hafterRank (larger - 1) (by omega) (by omega)
          (by simpa only [if_pos heven] using hlargerLow)
        dsimp [shift] at hstraddle
        split_ifs at hstraddle <;> omega
      · rw [if_neg heven] at hnewSide
        omega
    by_cases hfirstBefore : first < minimumIndex
    · rw [hgetBefore first hfirstBefore] at hfirstLow hstraddle
      rw [hnewAlpha, hshiftOrder] at hfirstLow
      by_cases hlargerNew : larger = minimumIndex
      · subst larger
        rw [hgetAt] at hlargerLow hstraddle
        by_cases heven : minimumIndex % 2 = 0
        · have hbefore := hbeforeRank first hfirstBefore
            (by simpa only [if_pos heven] using hfirstLow)
          dsimp [shift] at hstraddle
          split_ifs at hstraddle; omega
        · rw [if_neg heven] at hnewSide
          omega
      · rw [hgetOld larger hlargerBound hlargerNew] at hlargerLow hstraddle
        rw [hnewAlpha, hshiftOrder] at hlargerLow
        have htail := hlowerBefore first (oldIndex larger) hfirstBefore
          (by dsimp [oldIndex]; split_ifs <;> omega) (holdBounds larger hlargerBound hlargerNew)
          hfirstLow hlargerLow
        have hh := (hshiftOrder (value (oldIndex larger)) (value first)).mpr htail
        omega
    have hfirstAfter : minimumIndex < first := by omega
    have hsmallerAfter : minimumIndex < smaller := by omega
    have hlargerAfter : minimumIndex < larger := by omega
    rw [hgetAfter first hfirstAfter (by omega)] at hfirstLow hstraddle
    rw [hgetAfter smaller hsmallerAfter hsmallerBound] at hsmallerLow hstraddle
    rw [hgetAfter larger hlargerAfter hlargerBound] at hlargerLow hstraddle
    rw [hnewAlpha, hshiftOrder] at hfirstLow hsmallerLow hlargerLow
    rw [hshiftOrder, hshiftOrder] at hstraddle
    exact hlower (first - 1) (smaller - 1) (larger - 1) (by omega) (by omega) (by omega)
      (by omega) (by omega) hfirstLow hsmallerLow hlargerLow hstraddle
  have hshiftBonds : ∀ first second, first ≠ second + 1 → second ≠ first + 1 →
      shift first ≠ shift second + 1 ∧ shift second ≠ shift first + 1 := by
    intro first second hfirst hsecond
    dsimp [shift]; split_ifs <;> constructor <;> omega
  have hmemberBonds : ∀ index, index + 1 < member.length →
      newValue index ≠ newValue (index + 1) + 1 ∧
      newValue (index + 1) ≠ newValue index + 1 := by
    intro index hindex
    by_cases hbefore : index + 1 < minimumIndex
    · rw [hgetBefore index (by omega), hgetBefore (index + 1) hbefore]
      exact hshiftBonds _ _ (hbonds index (by omega)).1 (hbonds index (by omega)).2
    by_cases hleft : index + 1 = minimumIndex
    · have hindexEq : index = minimumIndex - 1 := by omega
      have hentry := hprefixValue index (by omega)
      rw [hgetBefore index (by omega), hleft, hgetAt]
      dsimp [shift, rank, half] at *
      split_ifs at hentry hrankSide ⊢ <;> constructor <;> omega
    by_cases hnew : index = minimumIndex
    · subst index
      rw [hgetAt, hmemberMinimum]
      constructor <;> omega
    rw [hgetAfter index (by omega) (by omega), hgetAfter (index + 1) (by omega) hindex]
    have hbond := hbonds (index - 1) (by omega)
    have heq : index - 1 + 1 = index := by omega
    simpa only [Nat.add_sub_cancel, heq] using hshiftBonds _ _ hbond.1 hbond.2
  have hclass := maximum_second_intervals member hmemberPerm (by omega) hmemberMaximum
    hmemberUpper hmemberLower
  have hfamilyMinimum : ∀ half : ℕ, 2 ≤ half → (member = P half ∨ member = E half) →
      (minimumIndex + 1) % 2 = 0 ∧ newValue 0 = (minimumIndex + 1) / 2 + 1 := by
    intro half hhalf heq
    rcases heq with heq | heq
    · have hlen : member.length = 2 * half := by rw [heq]; exact List.length_ofFn
      have hentry : (P half).getD (minimumIndex + 1) 0 = 1 := by
        simpa only [heq, newValue] using hmemberMinimum
      rw [List.getD_eq_getElem _ _ (by simp only [P, List.length_ofFn]; omega)] at hentry
      simp only [P, List.getElem_ofFn] at hentry
      have hhead : newValue 0 = half := by
        change member.getD 0 0 = half
        rw [heq, List.getD_eq_getElem _ _ (by simp only [P, List.length_ofFn]; omega)]
        simp only [P, List.getElem_ofFn, Nat.zero_mod, if_true, Nat.zero_div, Nat.sub_zero]
      split_ifs at hentry <;> constructor <;> omega
    · have hlen : member.length = 2 * half + 1 := by
        rw [heq]; simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
          List.length_singleton]
      have hminimumEq : minimumIndex + 1 = 2 * half := by
        by_contra hnot
        have hentry : (E half).getD (minimumIndex + 1) 0 = 1 := by
          simpa only [heq, newValue] using hmemberMinimum
        rw [List.getD_eq_getElem _ _ (by
          simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
            List.length_singleton]; omega)] at hentry
        simp only [E] at hentry
        rw [List.getElem_append_left (by
          simp only [List.length_map, P, List.length_ofFn]; omega), List.getElem_map] at hentry
        simp only [P, List.getElem_ofFn, Nat.succ_eq_add_one] at hentry
        split_ifs at hentry <;> omega
      have hhead : newValue 0 = half + 1 := by
        change member.getD 0 0 = half + 1
        rw [heq, List.getD_eq_getElem _ _ (by
          simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
            List.length_singleton]; omega)]
        simp only [E]
        rw [List.getElem_append_left (by simp only [List.length_map, P, List.length_ofFn]; omega),
          List.getElem_map]
        simp only [P, List.getElem_ofFn, Nat.zero_mod, if_true, Nat.zero_div, Nat.sub_zero,
          Nat.succ_eq_add_one]
      constructor <;> omega
  have hnotFamily : ∀ half : ℕ, 2 ≤ half → ¬ (member = P half ∨ member = E half) := by
    intro half hhalf heq
    obtain ⟨heven, hhead⟩ := hfamilyMinimum half hhalf heq
    have hodd : minimumIndex % 2 ≠ 0 := by omega
    have hside : alpha < rank := by
      have hh : alpha < rank ∧ rank ≤ permutation.length := by
        simpa only [if_neg hodd] using hrankSide
      exact hh.1
    have hnewHead : newValue 0 = alpha := by
      rw [hnewAlpha]
      dsimp [shift]; split_ifs <;> omega
    have hlastLower : value (minimumIndex - 1) = 2 := by
      rw [hprefixValue _ (by omega)]
      split_ifs <;> omega
    have hbond := (hbonds (minimumIndex - 1) (by omega)).1
    have hindexEq : minimumIndex - 1 + 1 = minimumIndex := by omega
    change value (minimumIndex - 1) ≠ permutation.getD (minimumIndex - 1 + 1) 0 + 1 at hbond
    rw [hindexEq, hminimum, hlastLower] at hbond
    omega
  have hmemberNotP : member ≠ P (member.length / 2) := by
    intro heq
    exact hnotFamily (member.length / 2) (by omega) (Or.inl heq)
  have hmemberNotE : member ≠ E (member.length / 2) := by
    intro heq
    exact hnotFamily (member.length / 2) (by omega) (Or.inr heq)
  have hmemberSimple : IsSimple member := by
    obtain hs | ⟨half, hhalf, heq⟩ := hclass.2.mp hmemberBonds
    · exact hs
    · have hlen : member.length = 2 * half + 1 := by
        rw [heq]; simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
          List.length_singleton]
      have hhalfEq : member.length / 2 = half := by omega
      exact False.elim (hmemberNotE (by simpa only [hhalfEq] using heq))
  refine ⟨hmemberPerm, hmemberMaximum, hmemberMinimum, hclass.1, hmemberSimple,
    hmemberNotP, hmemberNotE, ?_⟩
  change (((permutation.map shift).insertIdx minimumIndex rank).eraseIdx minimumIndex).map
    (fun entry => if rank < entry then entry - 1 else entry) = permutation
  rw [List.eraseIdx_insertIdx_self, List.map_map]
  calc
    _ = permutation.map id := by
      apply List.map_congr_left
      intro entry _
      dsimp [shift]
      split_ifs <;> omega
    _ = permutation := List.map_id _

end D5.S3.Combinatorics.PopStack.PopStackMaximumInsertion
