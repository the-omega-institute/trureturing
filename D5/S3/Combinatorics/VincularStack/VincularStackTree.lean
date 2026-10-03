/- GID: D5/S3/Combinatorics/VincularStack/VincularStackTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackTree
   mirror-E: none(waiver:maximum-insertion-succession)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Prod.Lex]
   utility: none
   digest: Maximum deletion and priority ranks give the complete invertible succession rule. -/

import D5.S3.Combinatorics.VincularStack.VincularStackPriority
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackParents

open VincularStackDefs VincularStackBasic VincularStackMarkers VincularStackCuts
open scoped List

noncomputable def parentSiteEquiv (size : ℕ) :
    (Σ parent : sortable size, {site : Fin (size + 1) //
      parent.val.take site.val ++ (size + 1) :: parent.val.drop site.val ∈
        sortable (size + 1)}) ≃ sortable (size + 1) := by
  classical
  let ParentSites := Σ parent : sortable size, {site : Fin (size + 1) //
    parent.val.take site.val ++ (size + 1) :: parent.val.drop site.val ∈ sortable (size + 1)}
  let forward : ParentSites → sortable (size + 1) := fun pair =>
    ⟨pair.1.val.take pair.2.val.val ++ (size + 1) :: pair.1.val.drop pair.2.val.val,
      pair.2.property⟩
  have hparentLength (parent : sortable size) : parent.val.length = size := by
    have := parent.property.1.length_eq
    simpa only [List.length_range'] using this
  have hparentNot (parent : sortable size) : size + 1 ∉ parent.val := by
    intro hmem
    have hmemRange := parent.property.1.mem_iff.mp hmem
    obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp hmemRange
    omega
  have hprefixNot (parent : sortable size) (site : Fin (size + 1)) :
      size + 1 ∉ parent.val.take site.val := fun hmem =>
    hparentNot parent ((List.take_sublist site.val parent.val).subset hmem)
  have hinsertionErase (parent : sortable size) (site : Fin (size + 1)) :
      (parent.val.take site.val ++ (size + 1) :: parent.val.drop site.val).erase (size + 1) =
        parent.val := by
    rw [List.erase_append_right _ (hprefixNot parent site), List.erase_cons_head,
      List.take_append_drop]
  have hinsertionIndex (parent : sortable size) (site : Fin (size + 1)) :
      (parent.val.take site.val ++ (size + 1) :: parent.val.drop site.val).idxOf (size + 1) =
        site.val := by
    rw [List.idxOf_append_of_notMem (hprefixNot parent site), List.idxOf_cons_self,
      Nat.add_zero, List.length_take, hparentLength parent, Nat.min_eq_left (by omega)]
  have hinjective : Function.Injective forward := by
    intro left right heq
    rcases left with ⟨leftParent, leftSite⟩
    rcases right with ⟨rightParent, rightSite⟩
    have hwords := congrArg Subtype.val heq
    change leftParent.val.take leftSite.val.val ++
        (size + 1) :: leftParent.val.drop leftSite.val.val =
      rightParent.val.take rightSite.val.val ++
        (size + 1) :: rightParent.val.drop rightSite.val.val at hwords
    have hparentValues := congrArg (fun word : List ℕ => word.erase (size + 1)) hwords
    rw [hinsertionErase, hinsertionErase] at hparentValues
    have hparents : leftParent = rightParent := Subtype.ext hparentValues
    subst rightParent
    have hsiteValues := congrArg (fun word : List ℕ => word.idxOf (size + 1)) hwords
    rw [hinsertionIndex, hinsertionIndex] at hsiteValues
    have hsites : leftSite = rightSite := Subtype.ext (Fin.ext hsiteValues)
    subst rightSite
    rfl
  let inverseData : (child : sortable (size + 1)) →
      {pair : ParentSites // forward pair = child} := by
    intro child
    have hchildLength : child.val.length = size + 1 := by
      have := child.property.1.length_eq
      simpa only [List.length_range'] using this
    have hmaximumMem : size + 1 ∈ child.val := by
      apply child.property.1.mem_iff.mpr
      exact List.mem_range'.mpr ⟨size, by omega, by omega⟩
    have hindex : child.val.idxOf (size + 1) < child.val.length :=
      List.idxOf_lt_length_iff.mpr hmaximumMem
    let site : Fin (size + 1) := ⟨child.val.idxOf (size + 1), by omega⟩
    let front := child.val.take site.val
    let suffix := child.val.drop (site.val + 1)
    have hfrontLength : front.length = site.val := List.length_take_of_le (by omega)
    have hsplit : child.val = front ++ (size + 1) :: suffix := by
      have htake := List.take_append_drop site.val child.val
      rw [List.drop_eq_getElem_cons (by exact hindex)] at htake
      rw [List.getElem_idxOf hindex] at htake
      exact htake.symm
    have hchildNodup : child.val.Nodup :=
      child.property.1.nodup_iff.mpr (List.nodup_range')
    have hwholeNodup : (front ++ (size + 1) :: suffix).Nodup := by rwa [← hsplit]
    have hfrontNot : size + 1 ∉ front := by
      intro hmem
      exact (List.nodup_append.mp hwholeNodup).2.2 (size + 1) hmem (size + 1)
        List.mem_cons_self rfl
    have hchildErase : child.val.erase (size + 1) = front ++ suffix := by
      rw [hsplit, List.erase_append_right _ hfrontNot, List.erase_cons_head]
    have hrangeNot : size + 1 ∉ List.range' 1 size := by
      intro hmem
      obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp hmem
      omega
    have hrangeErase : (List.range' 1 (size + 1)).erase (size + 1) =
        List.range' 1 size := by
      rw [List.range'_1_concat]
      have hlast : 1 + size = size + 1 := by omega
      rw [hlast, List.erase_append_right _ hrangeNot, List.erase_cons_head]
      simp
    have hparentPerm : (front ++ suffix).Perm (List.range' 1 size) := by
      have hperm := child.property.1.erase (size + 1)
      rwa [hchildErase, hrangeErase] at hperm
    have hparentNodup : (front ++ suffix).Nodup :=
      hparentPerm.nodup_iff.mpr (List.nodup_range')
    have hbound : ∀ value ∈ front ++ suffix, value < size + 1 := by
      intro value hvalue
      obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hparentPerm.mem_iff.mp hvalue)
      omega
    have hnil : ¬ ContainsV [] := by
      rintro ⟨position, hposition, _⟩
      simp at hposition
    have houtputPerm : (SC (front ++ suffix)).Perm (front ++ suffix) := by
      simpa [SC] using (process_preserves (front ++ suffix) [] hnil).1
    have hmarker := (maximum_insertion front suffix (size + 1) hbound).1
    have houtsplit := List.take_append_drop (outputGap front suffix) (SC (front ++ suffix))
    have hcut := (maximum_cut
      ((SC (front ++ suffix)).take (outputGap front suffix))
      ((SC (front ++ suffix)).drop (outputGap front suffix)) (size + 1)
      (by rw [houtsplit]; exact houtputPerm.nodup_iff.mpr hparentNodup)
      (by
        rw [houtsplit]
        intro value hvalue
        exact hbound value (houtputPerm.mem_iff.mp hvalue))).mp
      (by rw [← hmarker, ← hsplit]; exact child.property.2)
    have hparentAvoid : ¬ Contains231 (SC (front ++ suffix)) := by
      simpa only [houtsplit] using hcut.1
    let parent : sortable size := ⟨front ++ suffix, hparentPerm, hparentAvoid⟩
    have hreconstruct : parent.val.take site.val ++ (size + 1) :: parent.val.drop site.val =
        child.val := by
      change (front ++ suffix).take site.val ++ (size + 1) ::
        (front ++ suffix).drop site.val = child.val
      rw [← hfrontLength, List.take_append_length, List.drop_append_length]
      exact hsplit.symm
    let pair : ParentSites := ⟨parent, ⟨site, by rw [hreconstruct]; exact child.property⟩⟩
    exact ⟨pair, Subtype.ext hreconstruct⟩
  exact
    { toFun := forward
      invFun := fun child => (inverseData child).val
      left_inv := fun pair => hinjective (inverseData (forward pair)).property
      right_inv := fun child => (inverseData child).property }

end D5.S3.Combinatorics.VincularStack.VincularStackParents

namespace D5.S3.Combinatorics.VincularStack.VincularStackTree

open VincularStackDefs VincularStackBasic VincularStackCuts VincularStackMarkers
open VincularStackRun VincularStackPriority
open scoped List

noncomputable def activeSites (word : List ℕ) (maximum : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (word.length + 1)).filter fun site =>
    ¬ Contains231 (SC (word.take site ++ maximum :: word.drop site))

theorem earlier_site_activity (front : List ℕ) (entry : ℕ) (middle suffix : List ℕ)
    (maximum larger : ℕ)
    (hnodup : (front ++ entry :: (middle ++ suffix)).Nodup)
    (hbound : ∀ value ∈ front ++ entry :: (middle ++ suffix), value < maximum)
    (hlarge : maximum < larger) (hfront : front ≠ [])
    (hactive : ¬ Contains231 (SC ((front ++ entry :: middle) ++ maximum :: suffix))) :
    ¬ Contains231 (SC (front ++ larger :: entry :: (middle ++ maximum :: suffix))) ↔
      ¬ Contains231 (SC (front ++ larger :: entry :: (middle ++ suffix))) ∧
        outputGap front (entry :: (middle ++ suffix)) ≤
          outputGap (front ++ entry :: middle) suffix := by
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have hvalues : ∀ value ∈ front ++ entry :: (middle ++ suffix), value < larger :=
    fun value hvalue => lt_trans (hbound value hvalue) hlarge
  have hmaximumBound : ∀ value ∈ (front ++ entry :: middle) ++ suffix,
      value < maximum := by
    simpa only [List.append_assoc, List.cons_append] using hbound
  have hmaximum := maximum_insertion (front ++ entry :: middle) suffix maximum hmaximumBound
  have hlarger := maximum_insertion front (entry :: (middle ++ suffix)) larger hvalues
  obtain ⟨left, between, right, hsplit, horder⟩ :=
    two_marker_order front entry middle suffix larger maximum hvalues hbound
  have houtputPerm : (SC (front ++ entry :: (middle ++ suffix))).Perm
      (front ++ entry :: (middle ++ suffix)) := by
    simpa [SC] using (process_preserves (front ++ entry :: (middle ++ suffix)) [] hnil).1
  have houtputNodup : (left ++ between ++ right).Nodup := by
    rw [← hsplit]
    exact houtputPerm.nodup_iff.mpr hnodup
  have houtputBound : ∀ value ∈ left ++ between ++ right, value < maximum := by
    rw [← hsplit]
    exact fun value hvalue => hbound value (houtputPerm.mem_iff.mp hvalue)
  rcases horder with ⟨hgap, hdouble, hleft, hbetween⟩ |
    ⟨hgap, hdouble, hleft, hbetween⟩
  · have hmaximumOutput : SC ((front ++ entry :: middle) ++ maximum :: suffix) =
        (left ++ between) ++ maximum :: right := by
      rw [hmaximum.1]
      simp only [List.append_assoc, List.cons_append]
      rw [hsplit, ← hbetween, List.take_append_length, List.drop_append_length]
      simp only [List.append_assoc]
    have hlargerOutput : SC (front ++ larger :: entry :: (middle ++ suffix)) =
        left ++ larger :: (between ++ right) := by
      rw [hlarger.1, hsplit, ← hleft, List.append_assoc,
        List.take_append_length, List.drop_append_length]
    have hbase : ¬ Contains231 ((left ++ between) ++ maximum :: right) := by
      rwa [hmaximumOutput] at hactive
    have hnot : maximum ∉ left ++ between ++ right := by
      intro hmem
      exact lt_irrefl maximum (houtputBound maximum hmem)
    have hperm : (left ++ (between ++ maximum :: right)).Perm
        (maximum :: (left ++ between ++ right)) := by
      have hmove : ((left ++ between) ++ maximum :: right).Perm
          (maximum :: ((left ++ between) ++ right)) := List.perm_middle
      simpa only [List.append_assoc] using hmove
    have hchildNodup : (left ++ (between ++ maximum :: right)).Nodup :=
      hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnot, houtputNodup⟩)
    have hchildBound : ∀ value ∈ left ++ (between ++ maximum :: right), value < larger := by
      intro value hvalue
      rcases List.mem_append.mp hvalue with hl | hrest
      · exact lt_trans (houtputBound value (by simp [hl])) hlarge
      · rcases List.mem_append.mp hrest with hb | hrest
        · exact lt_trans (houtputBound value (by simp [hb])) hlarge
        · rcases List.mem_cons.mp hrest with rfl | hr
          · exact hlarge
          · exact lt_trans (houtputBound value (by simp [hr])) hlarge
    have hcutEquiv : separatingCut (left ++ (between ++ maximum :: right)) left.length ↔
        separatingCut (left ++ (between ++ right)) left.length := by
      simp only [separatingCut, List.take_append_length, List.drop_append_length]
      constructor
      · intro hcut value hvalue other hother
        rcases List.mem_append.mp hother with hb | hr
        · exact hcut value hvalue other (List.mem_append_left _ hb)
        · exact hcut value hvalue other
            (List.mem_append_right _ (List.mem_cons_of_mem maximum hr))
      · intro hcut value hvalue other hother
        rcases List.mem_append.mp hother with hb | hrest
        · exact hcut value hvalue other (List.mem_append_left _ hb)
        · rcases List.mem_cons.mp hrest with rfl | hr
          · exact houtputBound value (by simp [hvalue])
          · exact hcut value hvalue other (List.mem_append_right _ hr)
    have htwoTest := maximum_cut left (between ++ maximum :: right) larger
      hchildNodup hchildBound
    have honeTest := maximum_cut left (between ++ right) larger
      (by simpa only [List.append_assoc] using houtputNodup)
      (by
        intro value hvalue
        exact lt_trans (houtputBound value (by
          simpa only [List.append_assoc] using hvalue)) hlarge)
    have hparent : ¬ Contains231 (left ++ (between ++ right)) := by
      have hparentTest := maximum_cut (left ++ between) right maximum
        houtputNodup houtputBound
      simpa only [List.append_assoc] using (hparentTest.mp hbase).1
    rw [hdouble, hlargerOutput]
    constructor
    · intro hnot
      exact ⟨honeTest.mpr ⟨hparent, hcutEquiv.mp (htwoTest.mp hnot).2⟩, hgap⟩
    · rintro ⟨hone, _⟩
      exact htwoTest.mpr ⟨by simpa only [List.append_assoc] using hbase,
        hcutEquiv.mpr (honeTest.mp hone).2⟩
  · have hgaplt := hlarger.2 hfront
    have houtputLength := houtputPerm.length_eq
    have hright : right ≠ [] := by
      intro heq
      rw [heq, List.append_nil] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons] at hgaplt houtputLength
      simp only [List.length_append] at hlen hbetween
      omega
    cases right with
    | nil => exact False.elim (hright rfl)
    | cons last rest =>
      have hlast : last < maximum := houtputBound last (by simp)
      have hpattern : Contains231
          (left ++ maximum :: (between ++ larger :: last :: rest)) := by
        refine ⟨left.length, left.length + between.length + 1,
          left.length + between.length + 2, by omega, by omega, by simp; omega, ?_, ?_⟩
        · simp only [List.getD_append_right left _ 0 left.length (by omega), Nat.sub_self,
            List.getD_cons_zero]
          rw [List.getD_append_right left _ 0 (left.length + between.length + 2) (by omega)]
          simp only [Nat.add_assoc, Nat.add_sub_cancel_left, List.getD_cons_succ]
          rw [List.getD_append_right between _ 0 (between.length + 1) (by omega)]
          simpa using hlast
        · simp only [List.getD_append_right left _ 0 left.length (by omega), Nat.sub_self,
            List.getD_cons_zero]
          rw [List.getD_append_right left _ 0 (left.length + between.length + 1) (by omega)]
          simp only [Nat.add_assoc, Nat.add_sub_cancel_left, List.getD_cons_succ]
          rw [List.getD_append_right between _ 0 between.length (by omega)]
          simpa using hlarge
      rw [hdouble]
      constructor
      · exact fun hnot => False.elim (hnot hpattern)
      · rintro ⟨_, hless⟩
        omega

theorem succession_rule (word : List ℕ) (maximum larger : ℕ)
    (hnodup : word.Nodup) (hbound : ∀ value ∈ word, value < maximum)
    (hlarge : maximum < larger) (havoid : ¬ Contains231 (SC word)) :
    ∃ rank : (activeSites word maximum).erase 0 ≃
        Fin ((activeSites word maximum).card - 1),
      (activeSites (maximum :: word) larger).card = (activeSites word maximum).card + 1 ∧
      ∀ site : (activeSites word maximum).erase 0,
        (activeSites (word.take site.val ++ maximum :: word.drop site.val) larger).card =
          (rank site).val + 3 := by
  classical
  have child_count (front suffix : List ℕ) (maximum larger : ℕ)
      (hnodup : (front ++ suffix).Nodup)
      (hbound : ∀ value ∈ front ++ suffix, value < maximum) (hlarge : maximum < larger)
      (hactive : ¬ Contains231 (SC (front ++ maximum :: suffix))) :
      (activeSites (front ++ maximum :: suffix) larger).card =
        if front = [] then (activeSites (front ++ suffix) maximum).card + 1
        else 3 + ((activeSites (front ++ suffix) maximum).filter fun site =>
          0 < site ∧ (
            outputGap ((front ++ suffix).take site) ((front ++ suffix).drop site) <
              outputGap front suffix ∨
            outputGap ((front ++ suffix).take site) ((front ++ suffix).drop site) =
              outputGap front suffix ∧ site < front.length)).card := by
    classical
    let survivors := (activeSites (front ++ suffix) larger).filter fun site =>
      site ≠ front.length ∧ (site = 0 ∨
        outputGap ((front ++ suffix).take site) ((front ++ suffix).drop site) <
          outputGap front suffix ∨
        outputGap ((front ++ suffix).take site) ((front ++ suffix).drop site) =
          outputGap front suffix ∧ site < front.length)
    let translate (site : ℕ) := if site < front.length then site else site + 1
    have hnil : ¬ ContainsV [] := by
      rintro ⟨position, hposition, _⟩
      simp at hposition
    have hzero (word : List ℕ) (hword : word.Nodup)
        (hvalues : ∀ value ∈ word, value < larger) (havoid : ¬ Contains231 (SC word)) :
        0 ∈ activeSites word larger := by
      have hperm : (SC word).Perm word := by
        simpa [SC] using (process_preserves word [] hnil).1
      have hout := (maximum_insertion [] word larger (by simpa using hvalues)).1
      have htest := maximum_cut (SC word) [] larger
        (by simpa using hperm.nodup_iff.mpr hword)
        (by simpa using fun value hmem => hvalues value (hperm.mem_iff.mp hmem))
      have hgap : outputGap [] word = (SC word).length := by
        simp [outputGap, hperm.length_eq]
      have hcut : separatingCut (SC word ++ []) (SC word).length := by
        simp [separatingCut]
      have houtavoid : ¬ Contains231 (SC (larger :: word)) := by
        change ¬ Contains231 (SC ([] ++ larger :: word))
        rw [hout]
        simpa [hgap] using htest.mpr ⟨by simpa using havoid, hcut⟩
      simpa [activeSites] using houtavoid
    have hparentPerm : (SC (front ++ suffix)).Perm (front ++ suffix) := by
      simpa [SC] using (process_preserves (front ++ suffix) [] hnil).1
    have hparentAvoid : ¬ Contains231 (SC (front ++ suffix)) := by
      have hinsert := (maximum_insertion front suffix maximum hbound).1
      have htest := maximum_cut ((SC (front ++ suffix)).take (outputGap front suffix))
        ((SC (front ++ suffix)).drop (outputGap front suffix)) maximum
        (by simpa using hparentPerm.nodup_iff.mpr hnodup)
        (by simpa using fun value hmem => hbound value (hparentPerm.mem_iff.mp hmem))
      have := (htest.mp (hinsert ▸ hactive)).1
      simpa using this
    have hchildPerm : (front ++ maximum :: suffix).Perm (maximum :: (front ++ suffix)) :=
      List.perm_middle
    have hmaxnot : maximum ∉ front ++ suffix := by
      intro hmem
      exact lt_irrefl maximum (hbound maximum hmem)
    have hchildNodup : (front ++ maximum :: suffix).Nodup :=
      hchildPerm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hmaxnot, hnodup⟩)
    have hchildBound : ∀ value ∈ front ++ maximum :: suffix, value < larger := by
      intro value hvalue
      rcases List.mem_cons.mp (hchildPerm.mem_iff.mp hvalue) with rfl | hmem
      · exact hlarge
      · exact lt_trans (hbound value hmem) hlarge
    have hlocal := adjacent_sites_active front suffix maximum larger hnodup hbound hlarge hactive
    have hlocalBefore : front.length ∈ activeSites (front ++ maximum :: suffix) larger := by
      simpa [activeSites, List.take_append_length, List.drop_append_length] using hlocal.1
    have hlocalAfter : front.length + 1 ∈ activeSites (front ++ maximum :: suffix) larger := by
      have hsplit : front ++ maximum :: suffix = (front ++ [maximum]) ++ suffix := by simp
      have hlen : front.length + 1 = (front ++ [maximum]).length := by simp
      simp only [activeSites, Finset.mem_filter, Finset.mem_range]
      refine ⟨by simp, ?_⟩
      rw [hsplit, hlen, List.take_append_length, List.drop_append_length]
      simpa only [List.append_assoc, List.singleton_append] using hlocal.2
    have htranslation (site : ℕ) (hsite : site ≤ (front ++ suffix).length)
        (hne : site ≠ front.length) :
        translate site ∈ activeSites (front ++ maximum :: suffix) larger ↔
          site ∈ survivors := by
      by_cases hsitezero : site = 0
      · subst site
        have hfrontpos : 0 < front.length := by omega
        have hparentZero := hzero (front ++ suffix) hnodup
          (fun value hmem => lt_trans (hbound value hmem) hlarge) hparentAvoid
        have hchildZero := hzero (front ++ maximum :: suffix) hchildNodup hchildBound hactive
        simp only [translate, if_pos hfrontpos, survivors, Finset.mem_filter]
        exact ⟨fun _ => ⟨hparentZero, hne, Or.inl trivial⟩, fun _ => hchildZero⟩
      by_cases hbefore : site < front.length
      · let early := front.take site
        let entry := front[site]
        let middle := front.drop (site + 1)
        have hfrontSplit : front = early ++ entry :: middle := by
          simpa only [early, entry, middle, List.drop_eq_getElem_cons hbefore] using
            (List.take_append_drop site front).symm
        have hearlylen : early.length = site := by
          simp [early, List.length_take, Nat.min_eq_left (by omega : site ≤ front.length)]
        have hbaseSplit : front ++ suffix = early ++ entry :: (middle ++ suffix) := by
          rw [hfrontSplit]
          simp only [List.append_assoc, List.cons_append]
        have hchildSplit : front ++ maximum :: suffix =
            early ++ entry :: (middle ++ maximum :: suffix) := by
          rw [hfrontSplit]
          simp only [List.append_assoc, List.cons_append]
        have htest := earlier_site_activity early entry middle suffix maximum larger
          (by rwa [← hbaseSplit]) (by rwa [← hbaseSplit]) hlarge
          (by intro heq; simp [heq] at hearlylen; omega)
          (by rwa [← hfrontSplit])
        have htake : (front ++ suffix).take site = early := by
          rw [hbaseSplit, ← hearlylen, List.take_append_length]
        have hdrop : (front ++ suffix).drop site = entry :: (middle ++ suffix) := by
          rw [hbaseSplit, ← hearlylen, List.drop_append_length]
        have htakeChild : (front ++ maximum :: suffix).take site = early := by
          rw [hchildSplit, ← hearlylen, List.take_append_length]
        have hdropChild : (front ++ maximum :: suffix).drop site =
            entry :: (middle ++ maximum :: suffix) := by
          rw [hchildSplit, ← hearlylen, List.drop_append_length]
        simp only [translate, if_pos hbefore, survivors, activeSites, Finset.mem_filter,
          Finset.mem_range, htake, hdrop, htakeChild, hdropChild]
        rw [hfrontSplit]
        constructor
        · rintro ⟨hsize, havoid⟩
          obtain ⟨hparent, hgap⟩ := htest.mp havoid
          refine ⟨⟨by simp at hsite ⊢; omega, hparent⟩, ?_, ?_⟩
          · simpa only [← hfrontSplit] using hne
          · rcases lt_or_eq_of_le hgap with hlt | heq
            · exact Or.inr (Or.inl hlt)
            · exact Or.inr (Or.inr ⟨heq, by simpa only [← hfrontSplit] using hbefore⟩)
        · rintro ⟨⟨hsize, hparent⟩, _, hpriority⟩
          refine ⟨by simp at hsize ⊢; omega, htest.mpr ⟨hparent, ?_⟩⟩
          rcases hpriority with hzero' | hlt | ⟨heq, _⟩
          · exact False.elim (hsitezero hzero')
          · exact le_of_lt hlt
          · exact le_of_eq heq
      · have hlater : front.length < site := by omega
        let block := suffix.take (site - front.length)
        let tail := suffix.drop (site - front.length)
        have hblocklen : block.length = site - front.length := by
          simp only [block, List.length_take]
          exact Nat.min_eq_left (by simp at hsite; omega)
        have hsuffixSplit : suffix = block ++ tail := (List.take_append_drop _ suffix).symm
        have hblockpos : 0 < block.length := by omega
        cases hblock : block with
        | nil => simp [hblock] at hblockpos
        | cons entry middle =>
          have hsuffix : suffix = entry :: (middle ++ tail) := by
            simpa only [hblock, List.cons_append] using hsuffixSplit
          have hprefixlen : (front ++ entry :: middle).length = site := by
            simp only [hblock, List.length_cons] at hblocklen
            simp only [List.length_append, List.length_cons]
            omega
          have hbaseSplit : front ++ suffix = (front ++ entry :: middle) ++ tail := by
            rw [hsuffix]
            simp only [List.append_assoc, List.cons_append]
          have hchildSplit : front ++ maximum :: suffix =
              (front ++ maximum :: entry :: middle) ++ tail := by
            rw [hsuffix]
            simp only [List.append_assoc, List.cons_append]
          have hchildPrefixLen : (front ++ maximum :: entry :: middle).length = site + 1 := by
            simp only [List.length_append, List.length_cons] at hprefixlen ⊢
            omega
          have htest := later_site_activity front entry middle tail maximum larger
            (by rwa [← hsuffix]) (by rwa [← hsuffix]) hlarge (by rwa [← hsuffix])
          have htake : (front ++ suffix).take site = front ++ entry :: middle := by
            rw [hbaseSplit, ← hprefixlen, List.take_append_length]
          have hdrop : (front ++ suffix).drop site = tail := by
            rw [hbaseSplit, ← hprefixlen, List.drop_append_length]
          have htakeChild : (front ++ maximum :: suffix).take (site + 1) =
              front ++ maximum :: entry :: middle := by
            rw [hchildSplit, ← hchildPrefixLen, List.take_append_length]
          have hdropChild : (front ++ maximum :: suffix).drop (site + 1) = tail := by
            rw [hchildSplit, ← hchildPrefixLen, List.drop_append_length]
          simp only [translate, if_neg hbefore, survivors, activeSites, Finset.mem_filter,
            Finset.mem_range, htake, hdrop, htakeChild, hdropChild]
          rw [hsuffix]
          simp only [List.append_assoc, List.cons_append] at htest ⊢
          constructor
          · rintro ⟨hsize, havoid⟩
            obtain ⟨hparent, hgap⟩ := htest.mp havoid
            exact ⟨⟨by
              simp only [List.length_append, List.length_cons] at hsite hprefixlen ⊢
              omega, hparent⟩,
              hne, Or.inr (Or.inl hgap)⟩
          · rintro ⟨⟨hsize, hparent⟩, _, hpriority⟩
            refine ⟨by
              simp only [List.length_append, List.length_cons] at hsize hprefixlen ⊢
              omega, htest.mpr ⟨hparent, ?_⟩⟩
            rcases hpriority with hzero' | hlt | ⟨_, hbefore'⟩
            · exact False.elim (hsitezero hzero')
            · exact hlt
            · omega
    let forward : (Fin 2 ⊕ survivors) → activeSites (front ++ maximum :: suffix) larger :=
      fun value => match value with
      | Sum.inl localSite => ⟨front.length + localSite.val, by
          have hlocalBound := localSite.isLt
          by_cases hlocalZero : localSite.val = 0
          · simpa [hlocalZero] using hlocalBefore
          · have hlocalOne : localSite.val = 1 := by omega
            simpa [hlocalOne] using hlocalAfter⟩
      | Sum.inr oldSite => ⟨translate oldSite.val, by
          have hmem := oldSite.property
          have hsize : oldSite.val ≤ (front ++ suffix).length := by
            simp only [survivors, activeSites, Finset.mem_filter, Finset.mem_range] at hmem
            omega
          exact (htranslation oldSite.val hsize (Finset.mem_filter.mp oldSite.property).2.1).mpr
            oldSite.property⟩
    let backward : activeSites (front ++ maximum :: suffix) larger → (Fin 2 ⊕ survivors) :=
      fun value => if hbeforeLocal : value.val = front.length then Sum.inl ⟨0, by omega⟩
        else if hafterLocal : value.val = front.length + 1 then Sum.inl ⟨1, by omega⟩
        else Sum.inr ⟨if value.val < front.length then value.val else value.val - 1, by
          have hmem := value.property
          simp only [activeSites, Finset.mem_filter, Finset.mem_range,
            List.length_append, List.length_cons] at hmem
          have hsite : (if value.val < front.length then value.val else value.val - 1) ≤
              (front ++ suffix).length := by split_ifs <;> simp <;> omega
          have hne : (if value.val < front.length then value.val else value.val - 1) ≠
              front.length := by split_ifs <;> omega
          apply (htranslation _ hsite hne).mp
          convert value.property using 1
          simp only [translate]
          split_ifs <;> omega⟩
    let equivalence : activeSites (front ++ maximum :: suffix) larger ≃ (Fin 2 ⊕ survivors) :=
      (show (Fin 2 ⊕ survivors) ≃ activeSites (front ++ maximum :: suffix) larger from
      { toFun := forward
        invFun := backward
        left_inv := by
          intro value
          cases value with
          | inl localSite =>
            have hlocalBound := localSite.isLt
            by_cases hlocalZero : localSite.val = 0
            · have heq : localSite = 0 := Fin.ext hlocalZero
              rw [heq]
              simp [backward, forward]
            · have hone : localSite.val = 1 := by omega
              have heq : localSite = 1 := Fin.ext hone
              rw [heq]
              simp [backward, forward]
          | inr oldSite =>
            have hne := (Finset.mem_filter.mp oldSite.property).2.1
            by_cases hbefore : oldSite.val < front.length
            · have hneAfter : oldSite.val ≠ front.length + 1 := by omega
              simp [backward, forward, translate, hbefore, ne_of_lt hbefore, hneAfter]
            · have hneBefore : oldSite.val + 1 ≠ front.length := by omega
              have hnotBefore : ¬ oldSite.val + 1 < front.length := by omega
              simp [backward, forward, translate, hbefore, hneBefore, hne, hnotBefore]
        right_inv := by
          intro value
          apply Subtype.ext
          by_cases hbefore : value.val = front.length
          · simp [backward, forward, hbefore]
          by_cases hafter : value.val = front.length + 1
          · simp [backward, forward, hafter]
          by_cases hsmall : value.val < front.length
          · simp [backward, forward, translate, hbefore, hafter, hsmall]
          · have hdecode : ¬ value.val - 1 < front.length := by omega
            simp [backward, forward, translate, hbefore, hafter, hsmall, hdecode]
            omega }).symm
    have hcard : (activeSites (front ++ maximum :: suffix) larger).card = 2 + survivors.card := by
      simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] using
        Fintype.card_congr equivalence
    have hmarkers : activeSites (front ++ suffix) larger =
        activeSites (front ++ suffix) maximum := by
      ext site
      simp only [activeSites, Finset.mem_filter, Finset.mem_range]
      by_cases hsize : site < (front ++ suffix).length + 1
      · simp only [hsize, true_and]
        let before := (front ++ suffix).take site
        let after := (front ++ suffix).drop site
        have hsplit : before ++ after = front ++ suffix := List.take_append_drop _ _
        have hbeforeLength : before.length = site := by
          simp only [before, List.length_take]
          exact Nat.min_eq_left (by omega)
        have hboundM : ∀ value ∈ before ++ after, value < maximum := by
          rwa [hsplit]
        have hboundN : ∀ value ∈ before ++ after, value < larger :=
          fun value hmem => lt_trans (hboundM value hmem) hlarge
        have hinsertM := (maximum_insertion before after maximum hboundM).1
        have hinsertN := (maximum_insertion before after larger hboundN).1
        let gap := outputGap before after
        let out := SC (before ++ after)
        have houtNodup : (out.take gap ++ out.drop gap).Nodup := by
          simpa [out, hsplit] using hparentPerm.nodup_iff.mpr hnodup
        have houtBound : ∀ value ∈ out.take gap ++ out.drop gap, value < maximum := by
          simpa [out, hsplit] using fun value hmem =>
            hbound value (hparentPerm.mem_iff.mp hmem)
        have htestM := maximum_cut (out.take gap) (out.drop gap) maximum houtNodup houtBound
        have htestN := maximum_cut (out.take gap) (out.drop gap) larger houtNodup
          (fun value hmem => lt_trans (houtBound value hmem) hlarge)
        change ¬ Contains231 (SC (before ++ larger :: after)) ↔
          ¬ Contains231 (SC (before ++ maximum :: after))
        rw [hinsertN, hinsertM]
        exact htestN.trans htestM.symm
      · simp only [hsize, false_and]
    have hzeroParent : 0 ∈ activeSites (front ++ suffix) maximum := by
      rw [← hmarkers]
      exact hzero (front ++ suffix) hnodup
        (fun value hmem => lt_trans (hbound value hmem) hlarge) hparentAvoid
    by_cases hfront : front = []
    · rw [if_pos hfront]
      have hsurvivors : survivors = (activeSites (front ++ suffix) maximum).erase 0 := by
        ext site
        simp only [survivors, hmarkers, Finset.mem_filter, Finset.mem_erase]
        rw [hfront]
        simp only [List.length_nil, List.nil_append]
        constructor
        · rintro ⟨hmem, hne, _⟩
          exact ⟨hne, hmem⟩
        · rintro ⟨hne, hmem⟩
          have hsize : site ≤ suffix.length := by
            simp only [activeSites, Finset.mem_filter, Finset.mem_range] at hmem
            omega
          have htake : suffix.take site ≠ [] := by
            intro heq
            have hlen := congrArg List.length heq
            simp only [List.length_take, List.length_nil,
              Nat.min_eq_left hsize] at hlen
            omega
          have hgap := (maximum_insertion (suffix.take site) (suffix.drop site) maximum
            (by simpa [hfront] using hbound)).2 htake
          simp only [List.take_append_drop] at hgap
          refine ⟨hmem, hne, Or.inr (Or.inl ?_)⟩
          simpa [outputGap] using hgap
      rw [hcard, hsurvivors, Finset.card_erase_of_mem hzeroParent]
      have hpos := Finset.card_pos.mpr ⟨0, hzeroParent⟩
      omega
    · rw [if_neg hfront]
      let earlier := (activeSites (front ++ suffix) maximum).filter fun site =>
        0 < site ∧ (
          outputGap ((front ++ suffix).take site) ((front ++ suffix).drop site) <
            outputGap front suffix ∨
          outputGap ((front ++ suffix).take site) ((front ++ suffix).drop site) =
            outputGap front suffix ∧ site < front.length)
      have hfrontpos : 0 < front.length := List.length_pos_iff.mpr hfront
      have hsurvivors : survivors = insert 0 earlier := by
        ext site
        simp only [survivors, earlier, hmarkers, Finset.mem_filter, Finset.mem_insert]
        by_cases hsitezero : site = 0
        · subst site
          simp [hzeroParent, Ne.symm hfrontpos.ne']
        · constructor
          · rintro ⟨hmem, _, hzero' | hlt | ⟨heq, hbefore⟩⟩
            · exact False.elim (hsitezero hzero')
            · exact Or.inr ⟨hmem, by omega, Or.inl hlt⟩
            · exact Or.inr ⟨hmem, by omega, Or.inr ⟨heq, hbefore⟩⟩
          · rintro (hzero' | ⟨hmem, hpositive, hpriority⟩)
            · exact False.elim (hsitezero hzero')
            · refine ⟨hmem, ?_, Or.inr hpriority⟩
              intro heq
              subst site
              simp only [List.take_append_length, List.drop_append_length] at hpriority
              rcases hpriority with hlt | ⟨_, hlt⟩ <;> omega
      have hzeroEarlier : 0 ∉ earlier := by simp [earlier]
      rw [hcard, hsurvivors, Finset.card_insert_of_notMem hzeroEarlier]
      change 2 + (earlier.card + 1) = 3 + earlier.card
      omega
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have hperm : (SC word).Perm word := by
    simpa [SC] using (process_preserves word [] hnil).1
  have hzero : 0 ∈ activeSites word maximum := by
    have hinsert := (maximum_insertion [] word maximum (by simpa using hbound)).1
    have hgap : outputGap [] word = (SC word).length := by
      simp [outputGap, hperm.length_eq]
    have htest := maximum_cut (SC word) [] maximum
      (by simpa using hperm.nodup_iff.mpr hnodup)
      (by simpa using fun value hmem => hbound value (hperm.mem_iff.mp hmem))
    have hactive : ¬ Contains231 (SC (maximum :: word)) := by
      change ¬ Contains231 (SC ([] ++ maximum :: word))
      rw [hinsert]
      simpa [hgap] using htest.mpr ⟨by simpa using havoid, by simp [separatingCut]⟩
    simpa [activeSites] using hactive
  let sites := (activeSites word maximum).erase 0
  let key : ℕ ↪ (ℕ ×ₗ ℕ) :=
    { toFun := fun site => toLex (outputGap (word.take site) (word.drop site), site)
      inj' := by
        intro first second heq
        exact congrArg (fun value => (ofLex value).2) heq }
  let keys := sites.map key
  have hkeys : keys.card = (activeSites word maximum).card - 1 := by
    simp only [keys, Finset.card_map, sites, Finset.card_erase_of_mem hzero]
  let rank : sites ≃ Fin ((activeSites word maximum).card - 1) :=
    (sites.equivMap key).trans (keys.orderIsoOfFin hkeys).symm.toEquiv
  have hrankOrder (first second : sites) :
      key first.val < key second.val ↔ rank first < rank second := by
    have horder := (keys.orderIsoOfFin hkeys).symm.lt_iff_lt
      (x := sites.equivMap key first) (y := sites.equivMap key second)
    exact horder.symm
  refine ⟨rank, ?_, ?_⟩
  · have hactive : ¬ Contains231 (SC (maximum :: word)) := by
      simpa only [activeSites, Finset.mem_filter, Finset.mem_range, List.take_zero,
        List.drop_zero, List.nil_append, Nat.zero_lt_succ, true_and] using hzero
    simpa using child_count [] word maximum larger
      (by simpa using hnodup) (by simpa using hbound) hlarge hactive
  · intro site
    have hsite := Finset.mem_erase.mp site.property
    have hsize : site.val ≤ word.length := by
      have hmem := hsite.2
      simp only [activeSites, Finset.mem_filter, Finset.mem_range] at hmem
      omega
    have hprefixLength : (word.take site.val).length = site.val := by
      simp only [List.length_take, Nat.min_eq_left hsize]
    have hprefix : word.take site.val ≠ [] := by
      intro heq
      simp only [heq, List.length_nil] at hprefixLength
      exact hsite.1 hprefixLength.symm
    have hactive : ¬ Contains231 (SC (word.take site.val ++ maximum :: word.drop site.val)) :=
      (Finset.mem_filter.mp hsite.2).2
    have hcount := child_count (word.take site.val) (word.drop site.val) maximum larger
      (by simpa using hnodup) (by simpa using hbound) hlarge hactive
    rw [if_neg hprefix] at hcount
    let predecessors := sites.filter fun other => key other < key site.val
    have hpredecessors :
        ((activeSites (word.take site.val ++ word.drop site.val) maximum).filter fun other =>
          0 < other ∧ (
            outputGap ((word.take site.val ++ word.drop site.val).take other)
              ((word.take site.val ++ word.drop site.val).drop other) <
                outputGap (word.take site.val) (word.drop site.val) ∨
            outputGap ((word.take site.val ++ word.drop site.val).take other)
              ((word.take site.val ++ word.drop site.val).drop other) =
                outputGap (word.take site.val) (word.drop site.val) ∧
              other < (word.take site.val).length)) = predecessors := by
      ext other
      simp only [List.take_append_drop, hprefixLength, predecessors, sites,
        Finset.mem_filter, Finset.mem_erase, Nat.pos_iff_ne_zero]
      change _ ↔ (other ≠ 0 ∧ other ∈ activeSites word maximum) ∧
        toLex (outputGap (word.take other) (word.drop other), other) <
          toLex (outputGap (word.take site.val) (word.drop site.val), site.val)
      rw [Prod.Lex.toLex_lt_toLex]
      tauto
    let forward : predecessors → Fin (rank site).val := fun other =>
      ⟨(rank ⟨other.val, (Finset.mem_filter.mp other.property).1⟩).val, by
        have hbefore := (Finset.mem_filter.mp other.property).2
        exact (hrankOrder ⟨other.val,
          (Finset.mem_filter.mp other.property).1⟩ site).mp hbefore⟩
    let backward : Fin (rank site).val → predecessors := fun position =>
      ⟨(rank.symm ⟨position.val, lt_trans position.isLt (rank site).isLt⟩).val, by
        apply Finset.mem_filter.mpr
        refine ⟨(rank.symm _).property, ?_⟩
        apply (hrankOrder _ site).mpr
        simp only [Equiv.apply_symm_apply]
        exact position.isLt⟩
    let predecessorEquiv : predecessors ≃ Fin (rank site).val :=
      { toFun := forward
        invFun := backward
        left_inv := by
          intro other
          apply Subtype.ext
          simp only [backward, forward]
          exact congrArg Subtype.val (rank.symm_apply_apply _)
        right_inv := by
          intro position
          apply Fin.ext
          simp only [forward, backward]
          exact congrArg Fin.val (rank.apply_symm_apply _) }
    have hpredecessorCard : predecessors.card = (rank site).val := by
      simpa only [Fintype.card_coe, Fintype.card_fin] using
        Fintype.card_congr predecessorEquiv
    rw [hpredecessors, hpredecessorCard] at hcount
    omega

end D5.S3.Combinatorics.VincularStack.VincularStackTree
