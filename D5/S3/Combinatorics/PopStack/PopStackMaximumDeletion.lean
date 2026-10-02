/- GID: D5/S3/Combinatorics/PopStack/PopStackMaximumDeletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMaximumDeletion
   mirror-E: none(waiver:maximum-second-continuation-inverse)
   anchors: []
   utility: none
   digest: Deleting the last alternating-prefix entry reverses maximum-second continuation. -/

import D5.S3.Combinatorics.PopStack.PopStackMaximumTerminal
import D5.S3.Combinatorics.PopStack.PopStackMaximumIntervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMaximumDeletion

open PopStackDefs PopStackParallel PopStackExtra PopStackMaximumPrefix
open PopStackMaximumTerminal PopStackMaximumIntervals

theorem maximum_second_deletion (permutation : List ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hlength : 5 ≤ permutation.length) (hmaximum : permutation.getD 1 0 = permutation.length)
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
    (minimumIndex : ℕ) (hminimumLater : 3 ≤ minimumIndex)
    (hminimumBound : minimumIndex < permutation.length)
    (hminimum : permutation.getD minimumIndex 0 = 1)
    (hnotP : permutation ≠ P (permutation.length / 2))
    (hnotE : permutation ≠ E (permutation.length / 2)) :
    let cut := minimumIndex - 1
    let rank := permutation.getD cut 0
    let down := fun entry => if rank < entry then entry - 1 else entry
    let predecessor := (permutation.eraseIdx cut).map down
    predecessor.Perm (List.range' 1 predecessor.length) ∧ InC predecessor ∧
      IsSimple predecessor ∧ predecessor.getD 1 0 = predecessor.length ∧
      predecessor.getD cut 0 = 1 ∧ predecessor ≠ P (predecessor.length / 2) ∧
      predecessor ≠ E (predecessor.length / 2) ∧
      let newRank := if cut % 2 = 0 then predecessor.getD 0 0 - cut / 2 + 1
        else predecessor.length - (cut - 1) / 2 + 1
      (predecessor.map (fun entry =>
        if newRank ≤ entry then entry + 1 else entry)).insertIdx cut newRank = permutation := by
  classical
  let value := fun index => permutation.getD index 0
  let alpha := value 0
  let cut := minimumIndex - 1
  let rank := value cut
  let down := fun entry => if rank < entry then entry - 1 else entry
  let predecessor := (permutation.eraseIdx cut).map down
  let newValue := fun index => predecessor.getD index 0
  let oldIndex := fun index => if index < cut then index else index + 1
  change predecessor.Perm (List.range' 1 predecessor.length) ∧ InC predecessor ∧
    IsSimple predecessor ∧ newValue 1 = predecessor.length ∧ newValue cut = 1 ∧
    predecessor ≠ P (predecessor.length / 2) ∧ predecessor ≠ E (predecessor.length / 2) ∧
    let newRank := if cut % 2 = 0 then newValue 0 - cut / 2 + 1
      else predecessor.length - (cut - 1) / 2 + 1
    (predecessor.map (fun entry =>
      if newRank ≤ entry then entry + 1 else entry)).insertIdx cut newRank = permutation
  have hcut : 2 ≤ cut ∧ cut + 1 = minimumIndex ∧ cut < permutation.length := by
    dsimp [cut]; omega
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
  have hprefix := maximum_second_prefix permutation hperm (by omega) hmaximum hupper hlower
    hbonds minimumIndex hminimumBound hminimum
  have hprefixValue : ∀ index, index < minimumIndex → value index =
      if index % 2 = 0 then alpha - index / 2 else permutation.length - index / 2 := hprefix
  have hupperRoom : alpha + minimumIndex / 2 ≤ permutation.length := by
    by_contra hnot
    have hposition : 2 * (permutation.length - alpha) + 1 < minimumIndex := by omega
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
    have hentry := hprefixValue index hindex
    split_ifs at hentry <;> constructor <;> omega
  have hclass := maximum_second_intervals permutation hperm (by omega) hmaximum hupper hlower
  have hsimple : IsSimple permutation := by
    obtain hs | ⟨half, hhalf, heq⟩ := hclass.2.mp hbonds
    · exact hs
    · have hlen : permutation.length = 2 * half + 1 := by
        rw [heq]; simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
          List.length_singleton]
      have hhalfEq : permutation.length / 2 = half := by omega
      exact False.elim (hnotE (by simpa only [hhalfEq] using heq))
  have hnotThin : ¬ (minimumIndex % 2 = 0 ∧ alpha = permutation.length - 2) := by
    rintro ⟨heven, hthin⟩
    have hminimumFour : minimumIndex = 4 := by omega
    have hhead : permutation.take 4 =
        [permutation.length - 2, permutation.length,
          permutation.length - 3, permutation.length - 1] := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_cons, List.length_nil]; omega
      · intro index hindex hlist
        have hindexFour : index < 4 := by simpa using hlist
        rw [List.getElem_take, ← List.getD_eq_getElem _ 0 (by omega)]
        change value index = _
        rw [hprefixValue index (by omega)]
        have hcases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;> (simp [hthin]; try omega)
    have hstart : permutation.length - 3 + 1 = permutation.length - 2 := by omega
    have hmiddle : permutation.length - 3 + 2 = permutation.length - 1 := by omega
    have hend : permutation.length - 3 + 3 = permutation.length := by omega
    have hsmall : ([1, 3, 0, 2] : List ℕ).Perm [0, 1, 2, 3] := by decide
    have hblock : (permutation.take 4).Perm (List.range' (permutation.length - 3) 4) := by
      rw [hhead]
      convert hsmall.map (fun entry => permutation.length - 3 + entry) using 1 <;>
        (simp [List.range'_succ, hstart, hmiddle, hend, Nat.add_assoc]; try omega)
    exact hsimple 0 4 (permutation.length - 3) (by omega) (by omega) (by omega)
      (by simpa only [List.drop_zero] using hblock)
  have hrankFormula : rank = if cut % 2 = 0 then alpha - cut / 2
      else permutation.length - cut / 2 := hprefixValue cut (by omega)
  have hrankNotMinimum : rank ≠ 1 := by
    intro heq
    have hh := hdistinct cut minimumIndex hcut.2.2 hminimumBound
      (by change rank = permutation.getD minimumIndex 0; rw [hminimum]; exact heq)
    omega
  have hrankBounds := hbounds cut hcut.2.2
  have hrankNotMaximum : rank ≠ permutation.length := by
    intro heq
    have hh := hdistinct cut 1 hcut.2.2 (by omega)
      (by change rank = permutation.getD 1 0; rw [hmaximum]; exact heq)
    omega
  have hrankSide : if cut % 2 = 0 then rank < alpha else alpha < rank := by
    have hh := hprefixSide cut (by omega)
    split_ifs <;> omega
  have hrank : 3 ≤ rank ∧ rank < permutation.length := by
    have hbond := (hbonds cut (by omega)).1
    change rank ≠ permutation.getD (cut + 1) 0 + 1 at hbond
    rw [hcut.2.1, hminimum] at hbond
    omega
  have hplusPosition : value (cut - 2) = rank + 1 := by
    have hentry := hprefixValue (cut - 2) (by omega)
    have hbound := hbounds (cut - 2) (by omega)
    split_ifs at hentry hrankFormula <;> omega
  have hrightMissing : value (cut - 1) ≠ rank - 1 := by
    have hentry := hprefixValue (cut - 1) (by omega)
    split_ifs at hentry hrankFormula hrankSide <;> omega
  have hleftMissing : 3 ≤ cut → value (cut - 3) ≠ rank - 1 := by
    intro hlarge
    have hentry := hprefixValue (cut - 3) (by omega)
    split_ifs at hentry hrankFormula hrankSide <;> omega
  have hboundary : ∀ index, index + 1 < permutation.length →
      ¬ ((value index = rank - 1 ∧ value (index + 1) = rank + 1) ∨
        (value index = rank + 1 ∧ value (index + 1) = rank - 1)) := by
    intro index hindex hpair
    rcases hpair with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · have hposition := hdistinct (index + 1) (cut - 2) hindex (by omega)
        (hsecond.trans hplusPosition.symm)
      have hindexEq : index = cut - 3 := by omega
      exact hleftMissing (by omega) (by simpa only [hindexEq] using hfirst)
    · have hposition := hdistinct index (cut - 2) (by omega) (by omega)
        (hfirst.trans hplusPosition.symm)
      have hnextEq : index + 1 = cut - 1 := by omega
      exact hrightMissing (by simpa only [hnextEq] using hsecond)
  have hprevious : 3 ≤ down (value (cut - 1)) := by
    have hentry := hprefixValue (cut - 1) (by omega)
    have hbound := hbounds (cut - 1) (by omega)
    by_cases heven : minimumIndex % 2 = 0
    · have hprevLow : value (cut - 1) < alpha := by
        have hh := hprefixSide (cut - 1) (by omega)
        omega
      have hrankHigh : alpha < rank := by split_ifs at hrankSide <;> omega
      have hpreviousNotTwo : value (cut - 1) ≠ 2 := by
        intro heq
        have hexhausted : permutation.getD 0 0 = minimumIndex / 2 + 1 := by
          change alpha = minimumIndex / 2 + 1
          split_ifs at hentry <;> omega
        obtain ⟨hterminal, hE⟩ | ⟨hterminal, hP⟩ := exhausted_lower_prefix permutation hperm
          (by omega) hmaximum hupper hlower hbonds minimumIndex (by omega) hminimumBound
          hminimum heven hexhausted
        · have hhalfEq : permutation.length / 2 = minimumIndex / 2 := by omega
          exact hnotE (by simpa only [hhalfEq] using hE)
        · have hhalfEq : permutation.length / 2 = minimumIndex / 2 + 1 := by omega
          exact hnotP (by simpa only [hhalfEq] using hP)
      have hpreviousNotOne : value (cut - 1) ≠ 1 := by
        intro heq
        have hh := hdistinct (cut - 1) minimumIndex (by omega) hminimumBound
          (by change value (cut - 1) = permutation.getD minimumIndex 0; rw [hminimum]; exact heq)
        omega
      dsimp [down]; split_ifs <;> omega
    · have hprevHigh : alpha < value (cut - 1) := by
        have hh := hprefixSide (cut - 1) (by omega)
        omega
      have hrankLow : rank < alpha := by split_ifs at hrankSide <;> omega
      dsimp [down]; split_ifs <;> omega
  have hremovedMem : ∀ entry, entry ∈ permutation.eraseIdx cut ↔
      1 ≤ entry ∧ entry ≤ permutation.length ∧ entry ≠ rank := by
    have hremovedPerm := (List.getElem_cons_eraseIdx_perm hcut.2.2).trans hperm
    have hentry : permutation[cut]'hcut.2.2 = rank :=
      (List.getD_eq_getElem _ _ hcut.2.2).symm
    rw [hentry] at hremovedPerm
    have hremovedNodup := hremovedPerm.nodup_iff.mpr (List.nodup_range' 1)
    have hmissing := (List.nodup_cons.mp hremovedNodup).1
    intro entry
    constructor
    · intro hmem
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp (List.mem_of_mem_eraseIdx hmem))
      exact ⟨by omega, by omega, fun heq => hmissing (heq ▸ hmem)⟩
    · rintro ⟨hpositive, hbound, hne⟩
      have hh : entry ∈ rank :: permutation.eraseIdx cut :=
        hremovedPerm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      exact (List.mem_cons.mp hh).resolve_left hne
  have hdownOrder : ∀ first second, first ≠ rank → second ≠ rank →
      (down first < down second ↔ first < second) := by
    intro first second hfirst hsecond
    dsimp [down]; split_ifs <;> omega
  have hpredecessorLength : predecessor.length = permutation.length - 1 := by
    simp only [predecessor, List.length_map, List.length_eraseIdx, if_pos hcut.2.2]
  have hpredecessorNodup : predecessor.Nodup := by
    apply (hnodup.eraseIdx cut).map_on
    intro first hfirst second hsecond heq
    have hfirstNe := ((hremovedMem first).mp hfirst).2.2
    have hsecondNe := ((hremovedMem second).mp hsecond).2.2
    dsimp [down] at heq
    split_ifs at heq <;> omega
  have hpredecessorPerm : predecessor.Perm (List.range' 1 predecessor.length) := by
    apply (List.perm_ext_iff_of_nodup hpredecessorNodup (List.nodup_range' _)).mpr
    intro entry
    rw [List.mem_range'_1, hpredecessorLength]
    change entry ∈ (permutation.eraseIdx cut).map down ↔ _
    constructor
    · intro hmem
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hmem
      have hh := (hremovedMem old).mp hold
      dsimp [down]; split_ifs <;> omega
    · rintro ⟨hpositive, hbound⟩
      by_cases hbelow : entry < rank
      · refine List.mem_map.mpr ⟨entry, (hremovedMem entry).mpr (by omega), ?_⟩
        dsimp [down]; split_ifs <;> omega
      · refine List.mem_map.mpr ⟨entry + 1, (hremovedMem _).mpr (by omega), ?_⟩
        dsimp [down]; split_ifs <;> omega
  have hget : ∀ index, index < predecessor.length →
      newValue index = down (value (oldIndex index)) := by
    intro index hindex
    change predecessor.getD index 0 = _
    rw [List.getD_eq_getElem _ _ hindex]
    change ((permutation.eraseIdx cut).map down)[index] = _
    rw [List.getElem_map, List.getElem_eraseIdx]
    dsimp only [oldIndex]
    split_ifs <;>
      rw [show value _ = permutation[_] from List.getD_eq_getElem _ _ (by omega)]
  have holdBounds : ∀ index, index < predecessor.length →
      oldIndex index < permutation.length := by
    intro index hindex
    dsimp [oldIndex]; split_ifs <;> omega
  have holdNotCut : ∀ index, oldIndex index ≠ cut := by
    intro index
    dsimp [oldIndex]; split_ifs <;> omega
  have holdOrder : ∀ first second, first < second → oldIndex first < oldIndex second := by
    intro first second horder
    dsimp [oldIndex]; split_ifs <;> omega
  have holdPositive : ∀ index, 2 ≤ index → 2 ≤ oldIndex index := by
    intro index hindex
    dsimp [oldIndex]; split_ifs <;> omega
  have holdNeRank : ∀ index, index < predecessor.length → value (oldIndex index) ≠ rank := by
    intro index hindex heq
    have hh := hdistinct (oldIndex index) cut (holdBounds index hindex) hcut.2.2 heq
    exact holdNotCut index hh
  have halphaNeRank : alpha ≠ rank := by
    intro heq
    have hh := hdistinct 0 cut (by omega) hcut.2.2 heq
    omega
  have hnewAlpha : newValue 0 = down alpha := by
    rw [hget 0 (by omega)]
    simp only [oldIndex, show 0 < cut by omega, if_true]
    rfl
  have hpredecessorMaximum : newValue 1 = predecessor.length := by
    rw [hget 1 (by omega)]
    simp only [oldIndex, show 1 < cut by omega, if_true, value, hmaximum]
    rw [hpredecessorLength]
    dsimp [down]; split_ifs <;> omega
  have hpredecessorMinimum : newValue cut = 1 := by
    rw [hget cut (by omega)]
    simp only [oldIndex, lt_self_iff_false, if_false, hcut.2.1, value, hminimum]
    dsimp [down]; split_ifs <;> omega
  have hpredecessorUpper : ∀ first second, 2 ≤ first → first < second →
      second < predecessor.length → newValue 0 < newValue first →
      newValue 0 < newValue second → newValue second < newValue first := by
    intro first second hfirst horder hsecond hfirstHigh hsecondHigh
    rw [hget first (by omega), hnewAlpha,
      hdownOrder alpha _ halphaNeRank (holdNeRank first (by omega))] at hfirstHigh
    rw [hget second hsecond, hnewAlpha,
      hdownOrder alpha _ halphaNeRank (holdNeRank second hsecond)] at hsecondHigh
    rw [hget first (by omega), hget second hsecond,
      hdownOrder _ _ (holdNeRank second hsecond) (holdNeRank first (by omega))]
    exact hupper _ _ (holdPositive first hfirst) (holdOrder first second horder)
      (holdBounds second hsecond) hfirstHigh hsecondHigh
  have hpredecessorLower : ∀ first smaller larger, 2 ≤ first → first < smaller →
      first < larger →
      smaller < predecessor.length → larger < predecessor.length →
      newValue first < newValue 0 → newValue smaller < newValue 0 →
      newValue larger < newValue 0 →
      ¬ (newValue smaller < newValue first ∧ newValue first < newValue larger) := by
    intro first smaller larger hfirst hsmaller hlarger hsmallerBound hlargerBound
      hfirstLow hsmallerLow hlargerLow hstraddle
    rw [hget first (by omega), hnewAlpha,
      hdownOrder _ alpha (holdNeRank first (by omega)) halphaNeRank] at hfirstLow
    rw [hget smaller hsmallerBound, hnewAlpha,
      hdownOrder _ alpha (holdNeRank smaller hsmallerBound) halphaNeRank] at hsmallerLow
    rw [hget larger hlargerBound, hnewAlpha,
      hdownOrder _ alpha (holdNeRank larger hlargerBound) halphaNeRank] at hlargerLow
    rw [hget first (by omega), hget smaller hsmallerBound, hget larger hlargerBound,
      hdownOrder _ _ (holdNeRank smaller hsmallerBound) (holdNeRank first (by omega)),
      hdownOrder _ _ (holdNeRank first (by omega)) (holdNeRank larger hlargerBound)] at hstraddle
    exact hlower _ _ _ (holdPositive first hfirst) (holdOrder first smaller hsmaller)
      (holdOrder first larger hlarger) (holdBounds smaller hsmallerBound)
      (holdBounds larger hlargerBound) hfirstLow hsmallerLow hlargerLow hstraddle
  have hdownBonds : ∀ index, index + 1 < permutation.length →
      index ≠ cut → index + 1 ≠ cut →
      down (value index) ≠ down (value (index + 1)) + 1 ∧
      down (value (index + 1)) ≠ down (value index) + 1 := by
    intro index hindex hfirstPosition hsecondPosition
    have hbond := hbonds index hindex
    have hfirst := hbounds index (by omega)
    have hsecond := hbounds (index + 1) hindex
    have hmissing := hboundary index hindex
    have hfirstNe : value index ≠ rank := by
      intro heq
      exact hfirstPosition (hdistinct index cut (by omega) hcut.2.2 heq)
    have hsecondNe : value (index + 1) ≠ rank := by
      intro heq
      exact hsecondPosition (hdistinct (index + 1) cut hindex hcut.2.2 heq)
    change value index ≠ value (index + 1) + 1 ∧
      value (index + 1) ≠ value index + 1 at hbond
    dsimp [down]; split_ifs <;> constructor <;> omega
  have hpredecessorBonds : ∀ index, index + 1 < predecessor.length →
      newValue index ≠ newValue (index + 1) + 1 ∧
      newValue (index + 1) ≠ newValue index + 1 := by
    intro index hindex
    rw [hget index (by omega), hget (index + 1) hindex]
    by_cases hbefore : index + 1 < cut
    · simp only [oldIndex, if_pos hbefore, if_pos (show index < cut by omega)]
      exact hdownBonds index (by omega) (by omega) (by omega)
    by_cases hgap : index + 1 = cut
    · have hindexEq : index = cut - 1 := by omega
      simp only [oldIndex, if_pos (show index < cut by omega), hgap, lt_self_iff_false, if_false,
        hcut.2.1, value, hminimum]
      change down (value index) ≠ down 1 + 1 ∧ down 1 ≠ down (value index) + 1
      have hprev : 3 ≤ down (value index) := by simpa only [hindexEq] using hprevious
      have hdownOne : down 1 = 1 := by dsimp [down]; split_ifs <;> omega
      rw [hdownOne]
      constructor <;> omega
    · simp only [oldIndex, if_neg (show ¬ index < cut by omega),
        if_neg (show ¬ index + 1 < cut by omega)]
      exact hdownBonds (index + 1) (by omega) (by omega) (by omega)
  have hnewRank : (if cut % 2 = 0 then newValue 0 - cut / 2 + 1
      else predecessor.length - (cut - 1) / 2 + 1) = rank := by
    rw [hnewAlpha, hpredecessorLength]
    dsimp [down]
    split_ifs at hrankFormula hrankSide ⊢ <;> omega
  have hfamilyMinimum : ∀ half : ℕ, 2 ≤ half →
      (predecessor = P half ∨ predecessor = E half) →
      cut % 2 = 0 ∧ newValue 0 = cut / 2 + 1 := by
    intro half hhalf heq
    rcases heq with heq | heq
    · have hlen : predecessor.length = 2 * half := by
        rw [heq]; exact List.length_ofFn
      have hentry : (P half).getD cut 0 = 1 := by simpa only [heq, newValue] using
        hpredecessorMinimum
      rw [List.getD_eq_getElem _ _ (by simp only [P, List.length_ofFn]; omega)] at hentry
      simp only [P, List.getElem_ofFn] at hentry
      have hhead : newValue 0 = half := by
        change predecessor.getD 0 0 = half
        rw [heq, List.getD_eq_getElem _ _ (by simp only [P, List.length_ofFn]; omega)]
        simp only [P, List.getElem_ofFn, Nat.zero_mod, if_true, Nat.zero_div, Nat.sub_zero]
      split_ifs at hentry <;> constructor <;> omega
    · have hlen : predecessor.length = 2 * half + 1 := by
        rw [heq]; simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
          List.length_singleton]
      have hcutBound : cut ≤ 2 * half := by omega
      have hcutEq : cut = 2 * half := by
        by_contra hnot
        have hentry : (E half).getD cut 0 = 1 := by simpa only [heq, newValue] using
          hpredecessorMinimum
        rw [List.getD_eq_getElem _ _ (by
          simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
            List.length_singleton]; omega)] at hentry
        simp only [E] at hentry
        rw [List.getElem_append_left (by simp only [List.length_map, P, List.length_ofFn]; omega),
          List.getElem_map] at hentry
        simp only [P, List.getElem_ofFn, Nat.succ_eq_add_one] at hentry
        split_ifs at hentry <;> omega
      have hhead : newValue 0 = half + 1 := by
        change predecessor.getD 0 0 = half + 1
        rw [heq, List.getD_eq_getElem _ _ (by
          simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
            List.length_singleton]; omega)]
        simp only [E]
        rw [List.getElem_append_left (by simp only [List.length_map, P, List.length_ofFn]; omega),
          List.getElem_map]
        simp only [P, List.getElem_ofFn, Nat.zero_mod, if_true, Nat.zero_div, Nat.sub_zero,
          Nat.succ_eq_add_one]
      constructor <;> omega
  have hpredecessorNotP : predecessor ≠ P (predecessor.length / 2) := by
    intro heq
    obtain ⟨heven, hhead⟩ := hfamilyMinimum (predecessor.length / 2) (by omega) (Or.inl heq)
    rw [if_pos heven, hhead] at hnewRank
    omega
  have hpredecessorNotE : predecessor ≠ E (predecessor.length / 2) := by
    intro heq
    obtain ⟨heven, hhead⟩ := hfamilyMinimum (predecessor.length / 2) (by omega) (Or.inr heq)
    rw [if_pos heven, hhead] at hnewRank
    omega
  have hpredecessorClass := maximum_second_intervals predecessor hpredecessorPerm (by omega)
    hpredecessorMaximum hpredecessorUpper hpredecessorLower
  have hpredecessorSimple : IsSimple predecessor := by
    obtain hs | ⟨half, hhalf, heq⟩ := hpredecessorClass.2.mp hpredecessorBonds
    · exact hs
    · have hlen : predecessor.length = 2 * half + 1 := by
        rw [heq]; simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
          List.length_singleton]
      have hhalfEq : predecessor.length / 2 = half := by omega
      exact False.elim (hpredecessorNotE (by simpa only [hhalfEq] using heq))
  refine ⟨hpredecessorPerm, hpredecessorClass.1, hpredecessorSimple, hpredecessorMaximum,
    hpredecessorMinimum, hpredecessorNotP, hpredecessorNotE, ?_⟩
  dsimp only
  rw [hnewRank]
  change (((permutation.eraseIdx cut).map down).map
    (fun entry => if rank ≤ entry then entry + 1 else entry)).insertIdx cut rank = permutation
  rw [List.map_map]
  have hmap : (permutation.eraseIdx cut).map
      ((fun entry => if rank ≤ entry then entry + 1 else entry) ∘ down) =
      permutation.eraseIdx cut := by
    calc
      _ = (permutation.eraseIdx cut).map id := by
        apply List.map_congr_left
        intro entry hentry
        have hmissing := ((hremovedMem entry).mp hentry).2.2
        dsimp [down]; split_ifs <;> omega
      _ = _ := List.map_id _
  rw [hmap]
  have hentry : rank = permutation[cut]'hcut.2.2 := List.getD_eq_getElem _ _ hcut.2.2
  rw [hentry]
  exact List.insertIdx_eraseIdx_getElem hcut.2.2

end D5.S3.Combinatorics.PopStack.PopStackMaximumDeletion
