/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentStates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentStates
   mirror-E: none(waiver:weak-ascent-inversion-states)
   anchors: [mathlib/module/Mathlib.Data.Finset.Range]
   utility: none
   digest: Inversion bottoms characterize the exact interval of admitted appended letters. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentGrowth
import Mathlib.Data.Finset.Range

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentStates

open WeakAscentDefs WeakAscentGrowth

noncomputable def inversionBottom (e : List ℕ) : ℕ := by
  classical
  exact (Finset.range e.length).sup fun bottom =>
    if ∃ top, top < bottom ∧ e.getD bottom 0 < e.getD top 0 then e.getD bottom 0 else 0

theorem last_extreme (e : List ℕ) (hempty : e ≠ []) (havoid : ¬ Contains210 e) :
    inversionBottom e ≤ e.foldr max 0 ∧
    inversionBottom e ≤ e.getLast?.getD 0 ∧
    (e.getLast?.getD 0 = e.foldr max 0 ∨
      e.getLast?.getD 0 = inversionBottom e ∧ inversionBottom e < e.foldr max 0) := by
  classical
  have hlength : 0 < e.length := List.length_pos_iff.mpr hempty
  have last_read : e.getD (e.length - 1) 0 = e.getLast?.getD 0 := by
    rw [List.getLast?_eq_some_getLast hempty, Option.getD_some,
      List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
  have read_bound (index : ℕ) (hindex : index < e.length) :
      e.getD index 0 ≤ e.foldr max 0 := by
    rw [List.getD_eq_getElem _ _ hindex]
    exact List.le_max_of_le (List.getElem_mem hindex) (Nat.le_refl _)
  have hmaximum : inversionBottom e ≤ e.foldr max 0 := by
    apply Finset.sup_le_iff.mpr
    intro bottom hbottom
    have hindex := Finset.mem_range.mp hbottom
    split
    · exact read_bound bottom hindex
    · exact Nat.zero_le _
  have hlast : inversionBottom e ≤ e.getLast?.getD 0 := by
    apply Finset.sup_le_iff.mpr
    intro bottom hbottom
    have hindex := Finset.mem_range.mp hbottom
    split
    · rename_i hinversion
      obtain ⟨top, htop, hvalues⟩ := hinversion
      by_contra hnot
      have hstrict : e.getLast?.getD 0 < e.getD bottom 0 := by omega
      have hbefore : bottom < e.length - 1 := by
        by_contra hnotbefore
        have heq : bottom = e.length - 1 := by omega
        rw [heq, last_read] at hstrict
        omega
      exact havoid ⟨top, bottom, e.length - 1, htop, hbefore, by omega,
        by rwa [last_read], hvalues⟩
    · exact Nat.zero_le _
  refine ⟨hmaximum, hlast, ?_⟩
  by_cases heq : e.getLast?.getD 0 = e.foldr max 0
  · exact Or.inl heq
  · have ha : e.getLast?.getD 0 < e.foldr max 0 := by
      have hbound := read_bound (e.length - 1) (by omega)
      rw [last_read] at hbound
      omega
    have max_member : e.foldr max 0 ∈ e := by
      have hmaxeq : e.foldr max 0 = e.max hempty := by
        apply Nat.le_antisymm
        · exact List.max_le_of_forall_le e _ fun value hvalue => List.le_max_of_mem hvalue
        · exact List.le_max_of_le (List.max_mem hempty) (Nat.le_refl _)
      rw [hmaxeq]
      exact List.max_mem hempty
    obtain ⟨top, htop, htopvalue⟩ := List.mem_iff_getElem.mp max_member
    have htopread : e.getD top 0 = e.foldr max 0 := by
      rw [List.getD_eq_getElem _ _ htop]
      exact htopvalue
    have hbefore : top < e.length - 1 := by
      by_contra hnot
      have heq : top = e.length - 1 := by omega
      rw [heq, last_read] at htopread
      omega
    have hinversion : ∃ top, top < e.length - 1 ∧
        e.getD (e.length - 1) 0 < e.getD top 0 :=
      ⟨top, hbefore, by rw [last_read, htopread]; exact ha⟩
    have hbottom := Finset.le_sup
      (f := fun bottom => if ∃ top, top < bottom ∧ e.getD bottom 0 < e.getD top 0
        then e.getD bottom 0 else 0)
      (Finset.mem_range.mpr (show e.length - 1 < e.length by omega))
    rw [if_pos hinversion, last_read] at hbottom
    change e.getLast?.getD 0 ≤ inversionBottom e at hbottom
    exact Or.inr ⟨Nat.le_antisymm hbottom hlast, by omega⟩

theorem append_interval (e : List ℕ) (hempty : e ≠ [])
    (he : IsWeakAscent e) (havoid : ¬ Contains210 e) (letter : ℕ) :
    IsWeakAscent (e ++ [letter]) ∧ ¬ Contains210 (e ++ [letter]) ↔
      inversionBottom e ≤ letter ∧ letter ≤ 1 + wasc e := by
  classical
  have hlength : 0 < e.length := List.length_pos_iff.mpr hempty
  have old_read (index : ℕ) (hindex : index < e.length) :
      (e ++ [letter]).getD index 0 = e.getD index 0 :=
    List.getD_append _ _ _ _ hindex
  have new_read : (e ++ [letter]).getD e.length 0 = letter := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp
  have weak_append : IsWeakAscent (e ++ [letter]) ↔ letter ≤ 1 + wasc e := by
    constructor
    · intro hweak
      have hbound := hweak e.length (by simp)
      rw [new_read, List.take_append_of_le_length (Nat.le_refl _),
        List.take_length] at hbound
      simpa [show e.length ≠ 0 by omega] using hbound
    · intro hbound index hindex
      have hindex' : index < e.length + 1 := by simpa using hindex
      by_cases hold : index < e.length
      · rw [old_read index hold, List.take_append_of_le_length (Nat.le_of_lt hold)]
        exact he index hold
      · have heq : index = e.length := by omega
        subst index
        rw [new_read, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
        simpa [show e.length ≠ 0 by omega] using hbound
  constructor
  · rintro ⟨hweak, hno⟩
    refine ⟨?_, weak_append.mp hweak⟩
    apply Finset.sup_le_iff.mpr
    intro bottom hbottom
    have hbottom' := Finset.mem_range.mp hbottom
    split
    · rename_i hinversion
      obtain ⟨top, htop, hvalues⟩ := hinversion
      by_contra hnot
      apply hno
      refine ⟨top, bottom, e.length, htop, hbottom', by simp, ?_, ?_⟩
      · rw [new_read, old_read bottom hbottom']
        omega
      · rw [old_read bottom hbottom', old_read top (by omega)]
        exact hvalues
    · exact Nat.zero_le _
  · rintro ⟨hbottom, hbound⟩
    refine ⟨weak_append.mpr hbound, ?_⟩
    rintro ⟨top, bottom, last, htop, hbottomlast, hlast, hvalues, hdescent⟩
    have hlast' : last < e.length + 1 := by simpa using hlast
    have hbottom' : bottom < e.length := by omega
    have htop' : top < e.length := by omega
    rw [old_read bottom hbottom', old_read top htop'] at hdescent
    by_cases hold : last < e.length
    · rw [old_read last hold, old_read bottom hbottom'] at hvalues
      exact havoid ⟨top, bottom, last, htop, hbottomlast, hold, hvalues, hdescent⟩
    · have heq : last = e.length := by omega
      subst last
      rw [new_read, old_read bottom hbottom'] at hvalues
      have hinversion : ∃ top, top < bottom ∧ e.getD bottom 0 < e.getD top 0 :=
        ⟨top, htop, hdescent⟩
      have hsup := Finset.le_sup
        (f := fun bottom => if ∃ top, top < bottom ∧ e.getD bottom 0 < e.getD top 0
          then e.getD bottom 0 else 0) (Finset.mem_range.mpr hbottom')
      simp only [if_pos hinversion] at hsup
      change e.getD bottom 0 ≤ inversionBottom e at hsup
      omega

theorem append_state (e : List ℕ) (letter : ℕ) :
    (e ++ [letter]).foldr max 0 = max (e.foldr max 0) letter ∧
    wasc (e ++ [letter]) = wasc e +
      (if e = [] then 0 else if e.getLast?.getD 0 ≤ letter then 1 else 0) ∧
    inversionBottom (e ++ [letter]) =
      if letter < e.foldr max 0 then max (inversionBottom e) letter else inversionBottom e := by
  classical
  have max_append (parent : List ℕ) :
      (parent ++ [letter]).foldr max 0 = max (parent.foldr max 0) letter := by
    induction parent with
    | nil => simp
    | cons first rest ih => simp [ih, max_assoc]
  have append_ascents (parent : List ℕ) :
      wasc (parent ++ [letter]) = wasc parent +
        if parent = [] then 0 else if parent.getLast?.getD 0 ≤ letter then 1 else 0 := by
    induction parent with
    | nil => simp [wasc]
    | cons first rest ih =>
      cases rest with
      | nil =>
        by_cases hpair : first ≤ letter <;> simp [wasc, hpair]
      | cons second tail =>
        simp only [List.cons_append, wasc, List.tail_cons, List.zip_cons_cons,
          List.filter_cons] at ih ⊢
        by_cases hpair : first ≤ second
        · simp [hpair, List.getLast?_cons_cons, List.cons_ne_nil] at ih ⊢
          omega
        · simp only [decide_eq_true_eq, hpair, reduceCtorEq, ↓reduceIte,
            List.getLast?_cons_cons] at ih ⊢
          exact ih
  refine ⟨max_append e, append_ascents e, ?_⟩
  have old_read (index : ℕ) (hindex : index < e.length) :
      (e ++ [letter]).getD index 0 = e.getD index 0 :=
    List.getD_append _ _ _ _ hindex
  have new_read : (e ++ [letter]).getD e.length 0 = letter := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp
  have new_inversion : (∃ top, top < e.length ∧
      (e ++ [letter]).getD e.length 0 < (e ++ [letter]).getD top 0) ↔
      letter < e.foldr max 0 := by
    constructor
    · rintro ⟨top, htop, hvalues⟩
      rw [new_read, old_read top htop] at hvalues
      have hbound : e.getD top 0 ≤ e.foldr max 0 := by
        rw [List.getD_eq_getElem _ _ htop]
        exact List.le_max_of_le (List.getElem_mem htop) (Nat.le_refl _)
      omega
    · intro hvalues
      by_contra hnot
      have hbound : e.foldr max 0 ≤ letter := by
        apply List.max_le_of_forall_le
        intro value hvalue
        obtain ⟨top, htop, htopvalue⟩ := List.mem_iff_getElem.mp hvalue
        have htopread : e.getD top 0 = value := by
          rw [List.getD_eq_getElem _ _ htop]
          exact htopvalue
        by_contra hnotle
        exact hnot ⟨top, htop, by rw [new_read, old_read top htop, htopread]; omega⟩
      omega
  have old_bottoms : (Finset.range e.length).sup
      (fun bottom => if ∃ top, top < bottom ∧
        (e ++ [letter]).getD bottom 0 < (e ++ [letter]).getD top 0
      then (e ++ [letter]).getD bottom 0 else 0) = inversionBottom e := by
    apply Finset.sup_congr rfl
    intro bottom hbottom
    have hbottom' := Finset.mem_range.mp hbottom
    have hinversion : (∃ top, top < bottom ∧
        (e ++ [letter]).getD bottom 0 < (e ++ [letter]).getD top 0) ↔
        ∃ top, top < bottom ∧ e.getD bottom 0 < e.getD top 0 := by
      constructor <;> rintro ⟨top, htop, hvalues⟩ <;>
        refine ⟨top, htop, ?_⟩
      · rwa [old_read bottom hbottom', old_read top (by omega)] at hvalues
      · rwa [old_read bottom hbottom', old_read top (by omega)]
    by_cases hex : ∃ top, top < bottom ∧ e.getD bottom 0 < e.getD top 0
    · rw [if_pos (hinversion.mpr hex), if_pos hex, old_read bottom hbottom']
    · rw [if_neg (fun hnew => hex (hinversion.mp hnew)), if_neg hex]
  conv_lhs => unfold inversionBottom
  rw [List.length_append, List.length_singleton, Finset.range_add_one,
    Finset.sup_insert, old_bottoms]
  by_cases hvalues : letter < e.foldr max 0
  · rw [if_pos (new_inversion.mpr hvalues), if_pos hvalues, new_read]
    exact max_comm _ _
  · rw [if_neg (fun hnew => hvalues (new_inversion.mp hnew)), if_neg hvalues]
    exact Nat.zero_max _

end D5.S3.Combinatorics.WeakAscent.WeakAscentStates
