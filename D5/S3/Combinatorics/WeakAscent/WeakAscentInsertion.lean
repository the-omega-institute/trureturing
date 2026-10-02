/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentInsertion
   mirror-E: none(waiver:vincular-maximum-insertion)
   anchors: [mathlib/module/Mathlib.Data.List.InsertIdx]
   utility: none
   digest: Deleting a maximum preserves avoidance and insertion has an exact site criterion. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentChildren
import Mathlib.Data.List.InsertIdx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentInsertion

open WeakAscentDefs

theorem delete_maximum_avoids (p : List ℕ) (site maximum : ℕ)
    (hsite : site ≤ p.length) (hmax : ∀ value ∈ p, value < maximum)
    (havoid : ¬ ContainsV2413 (p.insertIdx site maximum)) : ¬ ContainsV2413 p := by
  let shift (index : ℕ) := if index < site then index else index + 1
  have old_read (index : ℕ) :
      (p.insertIdx site maximum).getD (shift index) 0 = p.getD index 0 := by
    by_cases hbefore : index < site
    · simp [shift, hbefore, List.getD_eq_getElem?_getD, List.getElem?_insertIdx]
    · have hafter : ¬ index + 1 < site := by omega
      have hne : index + 1 ≠ site := by omega
      simp [shift, hbefore, List.getD_eq_getElem?_getD,
        List.getElem?_insertIdx, hafter, hne]
  have maximum_read : (p.insertIdx site maximum).getD site 0 = maximum := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hsite]
  have hlength : (p.insertIdx site maximum).length = p.length + 1 := by
    simp [List.length_insertIdx, hsite]
  rintro ⟨earlier, top, later, hearlier, hlater, hlast, hlow, hmid, hhigh⟩
  have hlift_earlier : shift earlier < shift top := by
    dsimp [shift]
    split_ifs <;> omega
  have hlift_later : shift top + 1 < shift later := by
    dsimp [shift]
    split_ifs <;> omega
  have hlift_length : shift later < (p.insertIdx site maximum).length := by
    rw [hlength]
    dsimp [shift]
    split_ifs <;> omega
  by_cases hcross : top + 1 = site
  · have hearlier' : shift earlier = earlier := by simp [shift, show earlier < site by omega]
    have hlater' : shift later = later + 1 := by
      simp [shift, show ¬ later < site by omega]
    have hbottom : shift (top + 1) = site + 1 := by simp [shift, hcross]
    have hlatermax : p.getD later 0 < maximum := by
      rw [List.getD_eq_getElem _ _ hlast]
      exact hmax _ (List.getElem_mem hlast)
    apply havoid
    refine ⟨earlier, site, later + 1, by omega, by omega, by rw [hlength]; omega,
      ?_, ?_, ?_⟩
    · rw [← hearlier', ← hbottom, old_read, old_read]
      exact hlow
    · rw [← hearlier', ← hlater', old_read, old_read]
      exact hmid
    · rw [maximum_read, ← hlater', old_read]
      exact hlatermax
  · have hadjacent : shift (top + 1) = shift top + 1 := by
      dsimp [shift]
      split_ifs <;> omega
    apply havoid
    refine ⟨shift earlier, shift top, shift later, hlift_earlier, hlift_later,
      hlift_length, ?_, ?_, ?_⟩
    · rw [← hadjacent, old_read, old_read]
      exact hlow
    · rw [old_read, old_read]
      exact hmid
    · rw [old_read, old_read]
      exact hhigh

theorem active_site_criterion (p : List ℕ) (site maximum : ℕ)
    (hsite : site ≤ p.length) (hmax : ∀ value ∈ p, value < maximum)
    (havoid : ¬ ContainsV2413 p) :
    ¬ ContainsV2413 (p.insertIdx site maximum) ↔
      ¬ ∃ earlier later, earlier < site ∧ site < later ∧ later < p.length ∧
        p.getD site 0 < p.getD earlier 0 ∧ p.getD earlier 0 < p.getD later 0 := by
  let q := p.insertIdx site maximum
  let unshift (index : ℕ) := if index < site then index else index - 1
  have hlength : q.length = p.length + 1 := by simp [q, List.length_insertIdx, hsite]
  have old_read (index : ℕ) (hne : index ≠ site) :
      q.getD index 0 = p.getD (unshift index) 0 := by
    by_cases hbefore : index < site
    · simp [q, unshift, hbefore, List.getD_eq_getElem?_getD, List.getElem?_insertIdx]
    · simp [q, unshift, hbefore, hne,
        List.getD_eq_getElem?_getD, List.getElem?_insertIdx]
  have maximum_read : q.getD site 0 = maximum := by
    simp [q, List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hsite]
  have qbound (index : ℕ) (hindex : index < q.length) : q.getD index 0 ≤ maximum := by
    rw [List.getD_eq_getElem _ _ hindex]
    have hmem := List.getElem_mem hindex
    change q[index] ∈ p.insertIdx site maximum at hmem
    rcases (List.mem_insertIdx hsite).mp hmem with heq | hold
    · omega
    · exact Nat.le_of_lt (hmax _ hold)
  have pbound (index : ℕ) (hindex : index < p.length) : p.getD index 0 < maximum := by
    rw [List.getD_eq_getElem _ _ hindex]
    exact hmax _ (List.getElem_mem hindex)
  constructor
  · intro hno
    rintro ⟨earlier, later, hearlier, hlater, hlast, hlow, hmid⟩
    apply hno
    refine ⟨earlier, site, later + 1, hearlier, by omega, by rw [hlength]; omega,
      ?_, ?_, ?_⟩
    · rw [old_read (site + 1) (by omega), old_read earlier (by omega)]
      simpa only [unshift, show ¬ site + 1 < site by omega, if_false,
        Nat.add_sub_cancel, if_pos hearlier] using hlow
    · rw [old_read earlier (by omega), old_read (later + 1) (by omega)]
      simpa only [unshift, if_pos hearlier, show ¬ later + 1 < site by omega,
        if_false, Nat.add_sub_cancel] using hmid
    · rw [maximum_read, old_read (later + 1) (by omega)]
      simpa only [unshift, show ¬ later + 1 < site by omega, if_false,
        Nat.add_sub_cancel] using pbound later hlast
  · intro hno
    rintro ⟨earlier, top, later, hearlier, hlater, hlast, hlow, hmid, hhigh⟩
    change later < q.length at hlast
    change q.getD (top + 1) 0 < q.getD earlier 0 at hlow
    change q.getD earlier 0 < q.getD later 0 at hmid
    change q.getD later 0 < q.getD top 0 at hhigh
    have hearlier_bound : earlier < q.length := by omega
    have htop_bound : top < q.length := by omega
    have hbottom_bound : top + 1 < q.length := by omega
    have hearlier_ne : earlier ≠ site := by
      intro heq
      have hbound := qbound later hlast
      rw [heq, maximum_read] at hmid
      omega
    have hbottom_ne : top + 1 ≠ site := by
      intro heq
      have hbound := qbound earlier hearlier_bound
      rw [heq, maximum_read] at hlow
      omega
    have hlater_ne : later ≠ site := by
      intro heq
      have hbound := qbound top htop_bound
      rw [heq, maximum_read] at hhigh
      omega
    by_cases htop_eq : top = site
    · subst top
      apply hno
      refine ⟨earlier, later - 1, hearlier, by omega, by omega, ?_, ?_⟩
      · rw [old_read (site + 1) (by omega), old_read earlier hearlier_ne] at hlow
        simpa only [unshift, show ¬ site + 1 < site by omega, if_false,
          Nat.add_sub_cancel, if_pos hearlier] using hlow
      · rw [old_read earlier hearlier_ne, old_read later hlater_ne] at hmid
        simpa only [unshift, if_pos hearlier, show ¬ later < site by omega,
          if_false] using hmid
    · have hadjacent : unshift (top + 1) = unshift top + 1 := by
        dsimp [unshift]
        split_ifs <;> omega
      have hearlier' : unshift earlier < unshift top := by
        dsimp [unshift]
        split_ifs <;> omega
      have hlater' : unshift top + 1 < unshift later := by
        dsimp [unshift]
        split_ifs <;> omega
      have hlast' : unshift later < p.length := by
        rw [hlength] at hlast
        dsimp [unshift]
        split_ifs <;> omega
      rw [old_read (top + 1) hbottom_ne, hadjacent,
        old_read earlier hearlier_ne] at hlow
      rw [old_read earlier hearlier_ne, old_read later hlater_ne] at hmid
      rw [old_read later hlater_ne, old_read top htop_eq] at hhigh
      exact havoid ⟨unshift earlier, unshift top, unshift later,
        hearlier', hlater', hlast', hlow, hmid, hhigh⟩

end D5.S3.Combinatorics.WeakAscent.WeakAscentInsertion
