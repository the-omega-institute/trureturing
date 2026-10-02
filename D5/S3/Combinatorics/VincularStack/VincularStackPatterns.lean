/- GID: D5/S3/Combinatorics/VincularStack/VincularStackPatterns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackPatterns
   mirror-E: none(waiver:classical-pattern-output-obstruction)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Prefix records and threshold restriction construct classical pattern obstructions. -/

import D5.S3.Combinatorics.VincularStack.VincularStackBasic
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackPrefixes

open VincularStackDefs VincularStackBasic VincularStackRun VincularStackMarkers

theorem no_pop_iff_records (input : List ℕ) :
    (snapshot input []).1 = [] ↔
      ∀ earlier next, earlier < next → next + 1 < input.length →
        input.getD (next + 1) 0 < input.getD next 0 →
        input.getD (next + 1) 0 ≤ input.getD earlier 0 := by
  have hpatternTail : ∀ front current : List ℕ,
      ContainsV current → ContainsV (front ++ current) := by
    intro front
    induction front with
    | nil => intro current hpattern; exact hpattern
    | cons top front inductionHypothesis =>
      intro current hpattern
      obtain ⟨position, hposition, later, hlater, hgap, hascent, hlower⟩ :=
        inductionHypothesis current hpattern
      refine ⟨position + 1, by simpa using hposition,
        later + 1, by simpa using hlater, by omega, ?_, ?_⟩ <;> simpa using ‹_›
  have hnoPop : ∀ word current : List ℕ, ¬ ContainsV current →
      ((snapshot word current).1 = [] ↔ ¬ ContainsV (word.reverse ++ current)) := by
    intro word
    induction word with
    | nil => intro current hcurrent; simpa [snapshot] using hcurrent
    | cons entry word inductionHypothesis =>
      intro current hcurrent
      cases current with
      | nil =>
        have hlegal : ¬ ContainsV [entry] := by
          rintro ⟨position, hposition, later, hlater, hgap, _, _⟩
          simp only [List.length_cons, List.length_nil] at hposition hlater
          omega
        simpa only [snapshot, Push, List.nil_append, List.reverse_cons,
          List.append_nil] using inductionHypothesis [entry] hlegal
      | cons top current =>
        by_cases hillegal : ContainsV (entry :: top :: current)
        · have hfinal := hpatternTail word.reverse (entry :: top :: current) hillegal
          simp only [snapshot, Push, if_pos hillegal, List.cons_append,
            List.cons_ne_nil, List.reverse_cons, List.append_assoc, List.cons_append,
            List.nil_append, hfinal, not_true_eq_false]
        · simpa only [snapshot, Push, if_neg hillegal, List.nil_append, List.reverse_cons,
            List.append_assoc, List.cons_append, List.nil_append]
            using inductionHypothesis (entry :: top :: current) hillegal
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  rw [hnoPop input [] hnil, List.append_nil]
  constructor
  · intro havoid earlier next hear hnext hdescent
    by_contra hnotminimum
    have hsmall : input.getD earlier 0 < input.getD (next + 1) 0 := by omega
    let position := input.length - next - 2
    let later := input.length - earlier - 1
    have hposition : position < input.length := by dsimp [position]; omega
    have hlater : later < input.length := by dsimp [later]; omega
    have hgap : position + 1 < later := by dsimp [position, later]; omega
    have hpositionRead : input.reverse.getD position 0 = input.getD (next + 1) 0 := by
      rw [List.getD_reverse position hposition]
      congr 1
      dsimp [position]
      omega
    have hnextRead : input.reverse.getD (position + 1) 0 = input.getD next 0 := by
      rw [List.getD_reverse (position + 1) (by omega)]
      congr 1
      dsimp [position]
      omega
    have hlaterRead : input.reverse.getD later 0 = input.getD earlier 0 := by
      rw [List.getD_reverse later hlater]
      congr 1
      dsimp [later]
      omega
    apply havoid
    refine ⟨position, by simpa using hposition, later, by simpa using hlater, hgap, ?_, ?_⟩
    · rw [hpositionRead, hnextRead]
      exact hdescent
    · rw [hlaterRead, hpositionRead]
      exact hsmall
  · intro hrecords hpattern
    obtain ⟨position, hposition, later, hlater, hgap, hascent, hlower⟩ := hpattern
    simp only [List.length_reverse] at hposition hlater
    rw [List.getD_reverse position hposition,
      List.getD_reverse (position + 1) (by omega)] at hascent
    rw [List.getD_reverse later hlater, List.getD_reverse position hposition] at hlower
    have hrecord := hrecords (input.length - 1 - later)
      (input.length - 1 - (position + 1)) (by omega) (by omega) (by
        have hindex : input.length - 1 - (position + 1) + 1 =
            input.length - 1 - position := by omega
        rw [hindex]
        exact hascent)
    have hindex : input.length - 1 - (position + 1) + 1 =
        input.length - 1 - position := by omega
    rw [hindex] at hrecord
    omega

end D5.S3.Combinatorics.VincularStack.VincularStackPrefixes

namespace D5.S3.Combinatorics.VincularStack.VincularStackSites

open VincularStackDefs VincularStackBasic VincularStackRun VincularStackMarkers
open VincularStackCuts VincularStackPrefixes

theorem separating_gap (front suffix : List ℕ) :
    separatingCut (SC (front ++ suffix)) (outputGap front suffix) ↔
      front = [] ∨
        ((∀ earlier next, earlier < next → next + 1 < front.length →
            front.getD (next + 1) 0 < front.getD next 0 →
            front.getD (next + 1) 0 ≤ front.getD earlier 0) ∧
          match suffix with
          | [] => True
          | entry :: _ =>
            (∃ lower ∈ (snapshot front []).2, lower < entry) ∨
              (∀ left ∈ suffix, ∀ right ∈ front, left < right)) := by
  rw [← no_pop_iff_records front]
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have hsplit : ∀ word unread current : List ℕ,
      Process (word ++ unread) current =
        (snapshot word current).1 ++ Process unread (snapshot word current).2 := by
    intro word
    induction word with
    | nil => intro unread current; rfl
    | cons entry word inductionHypothesis =>
      intro unread current
      simp only [List.cons_append, Process, snapshot, inductionHypothesis, List.append_assoc]
  have hlength (word : List ℕ) : (Process word []).length = word.length := by
    simpa using (process_preserves word [] hnil).1.length_eq
  by_cases hfront : front = []
  · subst front
    simp only [outputGap, if_true, List.nil_append]
    have hlen := hlength suffix
    simp only [SC] at ⊢
    rw [← hlen]
    simp [separatingCut]
  · simp only [hfront, false_or]
    obtain ⟨minimum, hminimum⟩ := Option.isSome_iff_exists.mp
      (List.isSome_min?_of_ne_nil hfront)
    obtain ⟨hminmem, hminbound⟩ := List.min?_eq_some_iff.mp hminimum
    obtain ⟨hstackavoid, hstackmin, hpopped, hprefixstate⟩ :=
      snapshot_minimum front [] minimum hnil (by simpa using hminmem)
        (by simpa using hminbound)
    have hstateperm :
        ((snapshot front []).1 ++ (snapshot front []).2).Perm front := by
      rw [← hprefixstate]
      simpa using (process_preserves front [] hnil).1
    have horiginal : SC (front ++ suffix) =
        (snapshot front []).1 ++ Process suffix (snapshot front []).2 := hsplit front suffix []
    have hforceEmpty : ∀ middle final : List ℕ, minimum ∈ final →
        separatingCut (((snapshot front []).1 ++ middle) ++ final)
          ((snapshot front []).1 ++ middle).length → (snapshot front []).1 = [] := by
      intro middle final hfinal hcut
      simp only [separatingCut, List.take_append_length, List.drop_append_length] at hcut
      cases hemitted : (snapshot front []).1 with
      | nil => rfl
      | cons value emitted =>
        have hvalue : value ∈ (snapshot front []).1 := by simp [hemitted]
        have := hcut value (List.mem_append_left _ hvalue) minimum hfinal
        have := hpopped value hvalue
        omega
    cases suffix with
    | nil =>
      have horig : SC front = (snapshot front []).1 ++ (snapshot front []).2 := by
        simpa only [List.append_nil, Process] using horiginal
      simp only [outputGap, if_neg hfront, List.append_nil, horig, and_true]
      constructor
      · intro hcut
        exact hforceEmpty [] (snapshot front []).2 hstackmin (by simpa using hcut)
      · intro hempty
        simp [hempty, separatingCut]
    | cons entry rest =>
      by_cases htemporary : ∃ lower ∈ (snapshot front []).2, lower < entry
      · simp only [outputGap, if_neg hfront, htemporary, if_true, true_or, and_true]
        constructor
        · intro hcut
          have hrunmin : minimum ∈ Process (entry :: rest) (snapshot front []).2 :=
            (process_preserves (entry :: rest) (snapshot front []).2 hstackavoid).2.subset hstackmin
          exact hforceEmpty [] (Process (entry :: rest) (snapshot front []).2) hrunmin
            (by simpa only [List.append_nil, horiginal] using hcut)
        · intro hempty
          simp [hempty, separatingCut]
      · have hentryStack : ∀ value ∈ (snapshot front []).2, entry ≤ value :=
          fun value hvalue => Nat.le_of_not_gt
            (fun hless => htemporary ⟨value, hvalue, hless⟩)
        have hlegal : ¬ ContainsV (entry :: (snapshot front []).2) := by
          cases hcurrent : (snapshot front []).2 with
          | nil => simp [hcurrent] at hstackmin
          | cons top current =>
            rw [push_test]
            rintro (hpattern | ⟨_, lower, hlower, hless⟩)
            · exact hstackavoid (by simpa [hcurrent] using hpattern)
            · have := hentryStack lower (by simp [hcurrent, hlower])
              omega
        have hprotected := protected_suffix rest [entry] (snapshot front []).2 entry hlegal
          (by simp) (by simp) hentryStack
        have hpushentry : Push entry (snapshot front []).2 =
            ([], entry :: (snapshot front []).2) := by
          cases hcurrent : (snapshot front []).2 with
          | nil => rfl
          | cons top current => simp only [Push, if_neg (by simpa [hcurrent] using hlegal)]
        have hold : Process (entry :: rest) (snapshot front []).2 =
            Process (entry :: rest) [] ++ (snapshot front []).2 := by
          simpa only [Process, Push, hpushentry, List.nil_append, List.cons_append]
            using hprotected
        have hgap : outputGap front (entry :: rest) =
            ((snapshot front []).1 ++ Process (entry :: rest) []).length := by
          simp only [outputGap, if_neg hfront, if_neg htemporary,
            List.length_append, List.length_cons]
          have hstatelength := hstateperm.length_eq
          have hrunlength := hlength (entry :: rest)
          simp only [List.length_append, List.length_cons] at hstatelength hrunlength ⊢
          omega
        have horig : SC (front ++ entry :: rest) =
            ((snapshot front []).1 ++ Process (entry :: rest) []) ++ (snapshot front []).2 := by
          rw [horiginal, hold, List.append_assoc]
        rw [hgap, horig]
        simp only [htemporary, false_or]
        constructor
        · intro hcut
          have hempty := hforceEmpty (Process (entry :: rest) []) (snapshot front []).2
            hstackmin hcut
          refine ⟨hempty, ?_⟩
          have hrunperm := (process_preserves (entry :: rest) [] hnil).1
          simp only [List.append_nil] at hrunperm
          have hstackperm : ((snapshot front []).2).Perm front := by
            simpa only [hempty, List.nil_append] using hstateperm
          simp only [separatingCut, List.take_append_length, List.drop_append_length,
            hempty, List.nil_append] at hcut
          intro left hleft right hright
          exact hcut left (hrunperm.mem_iff.mpr hleft) right (hstackperm.mem_iff.mpr hright)
        · rintro ⟨hempty, hrelation⟩
          have hrunperm := (process_preserves (entry :: rest) [] hnil).1
          simp only [List.append_nil] at hrunperm
          have hstackperm : ((snapshot front []).2).Perm front := by
            simpa only [hempty, List.nil_append] using hstateperm
          simp only [separatingCut, List.take_append_length, List.drop_append_length,
            hempty, List.nil_append]
          intro left hleft right hright
          exact hrelation left (hrunperm.mem_iff.mp hleft) right (hstackperm.mem_iff.mp hright)

end D5.S3.Combinatorics.VincularStack.VincularStackSites

namespace D5.S3.Combinatorics.VincularStack.VincularStackRestriction

open VincularStackDefs VincularStackBasic VincularStackMarkers

theorem restrict_sc (word : List ℕ) (hnodup : word.Nodup) (threshold : ℕ) :
    SC (word.filter (fun value => value ≤ threshold)) =
      (SC word).filter (fun value => value ≤ threshold) := by
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have hgeneral : ∀ size, ∀ current : List ℕ, current.length = size → current.Nodup →
      SC (current.filter (fun value => value ≤ threshold)) =
        (SC current).filter (fun value => value ≤ threshold) := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size inductionHypothesis =>
      intro current hsize hcurrent
      by_cases hempty : current = []
      · subst current
        rfl
      · obtain ⟨maximum, hmaximum⟩ := Option.isSome_iff_exists.mp
          (List.isSome_max?_of_ne_nil hempty)
        obtain ⟨hmaxmem, hmaxbound⟩ := List.max?_eq_some_iff.mp hmaximum
        by_cases hthreshold : maximum ≤ threshold
        · have hinputfilter : current.filter (fun value => value ≤ threshold) = current := by
            apply List.filter_eq_self.mpr
            intro value hvalue
            simpa using le_trans (hmaxbound value hvalue) hthreshold
          have houtperm : (SC current).Perm current := by
            simpa [SC] using (process_preserves current [] hnil).1
          have houtputfilter : (SC current).filter (fun value => value ≤ threshold) =
              SC current := by
            apply List.filter_eq_self.mpr
            intro value hvalue
            simpa using le_trans (hmaxbound value (houtperm.mem_iff.mp hvalue)) hthreshold
          rw [hinputfilter, houtputfilter]
        · obtain ⟨front, back, hsplit, _⟩ := List.eq_append_cons_of_mem hmaxmem
          subst current
          have hparentnodup : (front ++ back).Nodup :=
            ((List.Sublist.refl front).append (List.sublist_cons_self maximum back)).nodup hcurrent
          have hparentbound : ∀ value ∈ front ++ back, value < maximum := by
            intro value hvalue
            have hle : value ≤ maximum := by
              apply hmaxbound value
              rcases List.mem_append.mp hvalue with hfront | hback
              · exact List.mem_append_left _ hfront
              · exact List.mem_append_right _ (List.mem_cons_of_mem maximum hback)
            have hneq : value ≠ maximum := by
              intro heq
              subst value
              rcases List.mem_append.mp hvalue with hfront | hback
              · exact ((List.nodup_append.mp hcurrent).2.2 maximum hfront maximum
                  List.mem_cons_self) rfl
              · exact (List.nodup_cons.mp (List.nodup_append.mp hcurrent).2.1).1 hback
            omega
          have hparentsize : (front ++ back).length < size := by
            simp only [List.length_append, List.length_cons] at hsize ⊢
            omega
          have hparent := inductionHypothesis (front ++ back).length hparentsize
            (front ++ back) rfl hparentnodup
          have hmarker := (maximum_insertion front back maximum hparentbound).1
          have hfilterCons (rest : List ℕ) : (maximum :: rest).filter
              (fun value => value ≤ threshold) = rest.filter
              (fun value => value ≤ threshold) := by simp [hthreshold]
          have hfilterInput : (front ++ maximum :: back).filter
              (fun value => value ≤ threshold) = (front ++ back).filter
              (fun value => value ≤ threshold) := by
            simp only [List.filter_append, hfilterCons]
          have hfilterOutput : (SC (front ++ maximum :: back)).filter
              (fun value => value ≤ threshold) = (SC (front ++ back)).filter
              (fun value => value ≤ threshold) := by
            rw [hmarker]
            simp only [List.filter_append, hfilterCons]
            rw [← List.filter_append, List.take_append_drop]
          rw [hfilterInput, hfilterOutput]
          exact hparent
  exact hgeneral word.length word rfl hnodup

end D5.S3.Combinatorics.VincularStack.VincularStackRestriction

namespace D5.S3.Combinatorics.VincularStack.VincularStackPatterns

open VincularStackDefs VincularStackRestriction VincularStackBasic VincularStackRun
open VincularStackMarkers VincularStackCuts VincularStackSites VincularStackPrefixes
open scoped List

def Contains1324 (word : List ℕ) : Prop :=
  ∃ first second third fourth, first < second ∧ second < third ∧ third < fourth ∧
    fourth < word.length ∧ word.getD first 0 < word.getD third 0 ∧
    word.getD third 0 < word.getD second 0 ∧ word.getD second 0 < word.getD fourth 0

theorem contains1324_not_sortable (word : List ℕ) (hnodup : word.Nodup)
    (hpattern : Contains1324 word) : Contains231 (SC word) := by
  have maximum_prefix_obstruction : ∀ (front suffix : List ℕ) (maximum : ℕ),
      (front ++ suffix).Nodup →
      (∀ value ∈ front ++ suffix, value < maximum) →
      ¬ Contains231 (SC (front ++ maximum :: suffix)) →
      (snapshot front []).1 = [] ∧
        ∀ earlier middle later, earlier < middle → middle < later → later < front.length →
          ¬ (front.getD earlier 0 < front.getD later 0 ∧
            front.getD later 0 < front.getD middle 0) := by
    intro front suffix maximum hnodup hbound havoid
    have hnil : ¬ ContainsV [] := by
      rintro ⟨position, hposition, _⟩
      simp at hposition
    have hperm : (SC (front ++ suffix)).Perm (front ++ suffix) := by
      simpa [SC] using (process_preserves (front ++ suffix) [] hnil).1
    have hmarker := (maximum_insertion front suffix maximum hbound).1
    have hsplit : (SC (front ++ suffix)).take (outputGap front suffix) ++
        (SC (front ++ suffix)).drop (outputGap front suffix) = SC (front ++ suffix) :=
      List.take_append_drop _ _
    have hcut := (maximum_cut
      ((SC (front ++ suffix)).take (outputGap front suffix))
      ((SC (front ++ suffix)).drop (outputGap front suffix)) maximum
      (by rw [hsplit]; exact hperm.nodup_iff.mpr hnodup)
      (by rw [hsplit]; intro value hvalue; exact hbound value (hperm.mem_iff.mp hvalue))).mp
      (by rwa [← hmarker])
    have hgaple : outputGap front suffix ≤ (SC (front ++ suffix)).length := by
      by_cases hfront : front = []
      · rw [hperm.length_eq]
        simp [outputGap, hfront]
      · have hgap := (maximum_insertion front suffix maximum hbound).2 hfront
        rw [hperm.length_eq]
        omega
    have hseparate : separatingCut (SC (front ++ suffix)) (outputGap front suffix) := by
      simpa only [hsplit, List.length_take, Nat.min_eq_left hgaple] using hcut.2
    have hempty : (snapshot front []).1 = [] := by
      rcases (separating_gap front suffix).mp hseparate with hfront | hrecords
      · simp [hfront, snapshot]
      · exact (no_pop_iff_records front).mpr hrecords.1
    refine ⟨hempty, ?_⟩
    have hsilent : ∀ input stack : List ℕ, (snapshot input stack).1 = [] →
        (snapshot input stack).2 = input.reverse ++ stack := by
      intro input
      induction input with
      | nil => intro stack _; rfl
      | cons entry input inductionHypothesis =>
        intro stack hstate
        have hparts := List.append_eq_nil_iff.mp hstate
        have hpush : (Push entry stack).2 = entry :: stack := by
          cases stack with
          | nil => rfl
          | cons top stack =>
            by_cases hillegal : ContainsV (entry :: top :: stack)
            · simp [Push, hillegal] at hparts
            · simp [Push, hillegal]
        simpa only [snapshot, hpush, List.reverse_cons, List.append_assoc,
          List.cons_append, List.nil_append] using inductionHypothesis _ hparts.2
    have hstack : (snapshot front []).2 = front.reverse := by
      simpa using hsilent front [] hempty
    have hprocessSplit : ∀ input unread stack : List ℕ,
        Process (input ++ unread) stack =
          (snapshot input stack).1 ++ Process unread (snapshot input stack).2 := by
      intro input
      induction input with
      | nil => intro unread stack; rfl
      | cons entry input inductionHypothesis =>
        intro unread stack
        simp only [List.cons_append, Process, snapshot, inductionHypothesis, List.append_assoc]
    have hstackavoid : ¬ ContainsV front.reverse := by
      have hlegal : ∀ input stack : List ℕ, ¬ ContainsV stack →
          ¬ ContainsV (snapshot input stack).2 := by
        intro input
        induction input with
        | nil => intro stack hstack; exact hstack
        | cons entry input inductionHypothesis =>
          intro stack hstack
          exact inductionHypothesis _ (push_preserves entry stack hstack).1
      rw [← hstack]
      exact hlegal front [] hnil
    have hsub : front.reverse <+ SC (front ++ maximum :: suffix) := by
      rw [SC, hprocessSplit, hempty, hstack, List.nil_append]
      exact (process_preserves (maximum :: suffix) front.reverse hstackavoid).2
    obtain ⟨embedding, hread⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    intro earlier middle later hear hmid hlast hpattern
    let first : Fin front.reverse.length := ⟨front.length - 1 - later, by simp; omega⟩
    let second : Fin front.reverse.length := ⟨front.length - 1 - middle, by simp; omega⟩
    let third : Fin front.reverse.length := ⟨front.length - 1 - earlier, by simp; omega⟩
    have hfirstsecond : first < second := by
      change front.length - 1 - later < front.length - 1 - middle
      omega
    have hsecondthird : second < third := by
      change front.length - 1 - middle < front.length - 1 - earlier
      omega
    have houtputRead (index : Fin front.reverse.length) :
        (SC (front ++ maximum :: suffix)).getD (embedding index).val 0 =
          front.reverse.getD index.val 0 := by
      rw [List.getD_eq_getElem _ 0 (embedding index).isLt,
        List.getD_eq_getElem _ 0 index.isLt]
      exact (hread index).symm
    have hreverseRead (index : ℕ) (hindex : index < front.length) :
        front.reverse.getD (front.length - 1 - index) 0 = front.getD index 0 := by
      rw [List.getD_reverse _ (by omega)]
      congr 1
      omega
    apply havoid
    refine ⟨(embedding first).val, (embedding second).val, (embedding third).val,
      embedding.strictMono hfirstsecond, embedding.strictMono hsecondthird,
      (embedding third).isLt, ?_, ?_⟩
    · rw [houtputRead third, houtputRead first]
      dsimp only [first, third]
      rw [hreverseRead earlier (by omega), hreverseRead later hlast]
      exact hpattern.1
    · rw [houtputRead first, houtputRead second]
      dsimp only [first, second]
      rw [hreverseRead later hlast, hreverseRead middle (by omega)]
      exact hpattern.2
  by_contra havoid
  obtain ⟨first, second, third, fourth, hfirst, hsecond, hthird, hfourth,
    hlow, hmiddle, hhigh⟩ := hpattern
  let selected : List ℕ :=
    [word.getD first 0, word.getD second 0, word.getD third 0, word.getD fourth 0]
  let index (position : Fin selected.length) : ℕ :=
    if position.val = 0 then first else if position.val = 1 then second
      else if position.val = 2 then third else fourth
  have hindexbound (position : Fin selected.length) : index position < word.length := by
    dsimp only [index]
    split_ifs <;> omega
  let embedding : Fin selected.length ↪o Fin word.length :=
    OrderEmbedding.ofStrictMono (fun position => ⟨index position, hindexbound position⟩) (by
      intro left right hlt
      have hleft : left.val < 4 := left.isLt
      have hright : right.val < 4 := right.isLt
      change index left < index right
      have hltval : left.val < right.val := hlt
      dsimp only [index]
      split_ifs <;> omega)
  have hread (position : Fin selected.length) : selected.get position =
      word.get (embedding position) := by
    have hposition : position.val = 0 ∨ position.val = 1 ∨
        position.val = 2 ∨ position.val = 3 := by
      have := position.isLt
      simp only [selected, List.length_cons, List.length_nil] at this
      omega
    change selected[position.val] = word[index position]'(hindexbound position)
    rw [← List.getD_eq_getElem word 0 (hindexbound position)]
    rcases hposition with hzero | hone | htwo | hthree
    · simp only [selected, index, hzero, ↓reduceIte, List.getElem_cons_zero]
    · simp only [selected, index, hone, ↓reduceIte,
        List.getElem_cons_succ, List.getElem_cons_zero]
      rfl
    · simp only [selected, index, htwo, ↓reduceIte,
        List.getElem_cons_succ, List.getElem_cons_zero]
      rfl
    · simp only [selected, index, hthree,
        List.getElem_cons_succ, List.getElem_cons_zero]
      rfl
  have hsub : selected <+ word :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr ⟨embedding, hread⟩
  let maximum := word.getD fourth 0
  let restricted := word.filter (fun value => value ≤ maximum)
  have hfilterSelected : selected.filter (fun value => value ≤ maximum) = selected := by
    apply List.filter_eq_self.mpr
    intro value hvalue
    simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at hvalue
    simp only [decide_eq_true_eq]
    dsimp only [maximum]
    rcases hvalue with rfl | rfl | rfl | rfl <;> omega
  have hsubRestricted : selected <+ restricted := by
    simpa only [hfilterSelected] using hsub.filter (fun value => value ≤ maximum)
  obtain ⟨restrictedEmbedding, hrestrictedRead⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsubRestricted
  let maxPosition : Fin restricted.length := restrictedEmbedding ⟨3, by simp [selected]⟩
  let front := restricted.take maxPosition.val
  let suffix := restricted.drop (maxPosition.val + 1)
  have hmaxRead : restricted[maxPosition.val] = maximum := by
    simpa [selected, maxPosition, maximum] using
      (hrestrictedRead ⟨3, by simp [selected]⟩).symm
  have hsplit : restricted = front ++ maximum :: suffix := by
    have hconcat := List.take_append_drop maxPosition.val restricted
    rw [List.drop_eq_getElem_cons maxPosition.isLt, hmaxRead] at hconcat
    exact hconcat.symm
  have hrestrictedNodup : restricted.Nodup := hnodup.filter _
  have hparentNodup : (front ++ suffix).Nodup := by
    have hwhole : (front ++ maximum :: suffix).Nodup := by rwa [← hsplit]
    exact ((List.Sublist.refl front).append (List.sublist_cons_self maximum suffix)).nodup
      hwhole
  have hbound : ∀ value ∈ front ++ suffix, value < maximum := by
    intro value hvalue
    have hwholeMem : value ∈ restricted := by
      rw [hsplit]
      rcases List.mem_append.mp hvalue with hfront | hsuffix
      · exact List.mem_append_left _ hfront
      · exact List.mem_append_right _ (List.mem_cons_of_mem maximum hsuffix)
    have hle : value ≤ maximum := (List.mem_filter.mp hwholeMem).2 |> of_decide_eq_true
    have hneq : value ≠ maximum := by
      have hwhole : (front ++ maximum :: suffix).Nodup := by rwa [← hsplit]
      intro heq
      subst value
      rcases List.mem_append.mp hvalue with hfront | hsuffix
      · exact (List.nodup_append.mp hwhole).2.2 maximum hfront maximum
          List.mem_cons_self rfl
      · exact (List.nodup_cons.mp (List.nodup_append.mp hwhole).2.1).1 hsuffix
    omega
  have hrestrictedAvoid : ¬ Contains231 (SC restricted) := by
    rw [restrict_sc word hnodup maximum]
    intro hwitness
    obtain ⟨outputEmbedding, houtputRead⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (List.filter_sublist (p := fun value => value ≤ maximum) (l := SC word))
    obtain ⟨earlier, middle, later, hearlier, hmiddle, hlater, hsmall, hlarge⟩ := hwitness
    let earlierFin : Fin ((SC word).filter (fun value => value ≤ maximum)).length :=
      ⟨earlier, by omega⟩
    let middleFin : Fin ((SC word).filter (fun value => value ≤ maximum)).length :=
      ⟨middle, by omega⟩
    let laterFin : Fin ((SC word).filter (fun value => value ≤ maximum)).length :=
      ⟨later, hlater⟩
    have houtputGet (position : Fin ((SC word).filter
        (fun value => value ≤ maximum)).length) :
        (SC word).getD (outputEmbedding position).val 0 =
          ((SC word).filter (fun value => value ≤ maximum)).getD position.val 0 := by
      rw [List.getD_eq_getElem _ 0 (outputEmbedding position).isLt,
        List.getD_eq_getElem _ 0 position.isLt]
      exact (houtputRead position).symm
    apply havoid
    refine ⟨(outputEmbedding earlierFin).val, (outputEmbedding middleFin).val,
      (outputEmbedding laterFin).val, outputEmbedding.strictMono hearlier,
      outputEmbedding.strictMono hmiddle, (outputEmbedding laterFin).isLt, ?_, ?_⟩
    · rw [houtputGet laterFin, houtputGet earlierFin]
      exact hsmall
    · rw [houtputGet earlierFin, houtputGet middleFin]
      exact hlarge
  have hprefix := (maximum_prefix_obstruction front suffix maximum hparentNodup hbound
    (by rwa [← hsplit])).2
  let firstPosition := restrictedEmbedding ⟨0, by simp [selected]⟩
  let secondPosition := restrictedEmbedding ⟨1, by simp [selected]⟩
  let thirdPosition := restrictedEmbedding ⟨2, by simp [selected]⟩
  have hfirstSecond : firstPosition.val < secondPosition.val :=
    restrictedEmbedding.strictMono (by exact show (0 : ℕ) < 1 from by omega)
  have hsecondThird : secondPosition.val < thirdPosition.val :=
    restrictedEmbedding.strictMono (by exact show (1 : ℕ) < 2 from by omega)
  have hthirdMax : thirdPosition.val < maxPosition.val :=
    restrictedEmbedding.strictMono (by exact show (2 : ℕ) < 3 from by omega)
  have hfrontLength : front.length = maxPosition.val := by
    exact List.length_take_of_le (by omega)
  have hfrontRead (position : Fin selected.length) (hposition : position.val < 3) :
      front.getD (restrictedEmbedding position).val 0 = selected.get position := by
    have hlt : (restrictedEmbedding position).val < maxPosition.val :=
      restrictedEmbedding.strictMono hposition
    rw [List.getD_eq_getElem _ 0 (by omega)]
    change (restricted.take maxPosition.val)[(restrictedEmbedding position).val] = _
    rw [List.getElem_take]
    exact (hrestrictedRead position).symm
  apply hprefix firstPosition.val secondPosition.val thirdPosition.val
    hfirstSecond hsecondThird (by omega)
  constructor
  · simpa [firstPosition, thirdPosition, selected] using
      (show front.getD firstPosition.val 0 < front.getD thirdPosition.val 0 from by
        rw [hfrontRead ⟨0, by simp [selected]⟩ (by exact show (0 : ℕ) < 3 from by omega),
          hfrontRead ⟨2, by simp [selected]⟩ (by exact show (2 : ℕ) < 3 from by omega)]
        exact hlow)
  · rw [hfrontRead ⟨2, by simp [selected]⟩ (by exact show (2 : ℕ) < 3 from by omega),
      hfrontRead ⟨1, by simp [selected]⟩ (by exact show (1 : ℕ) < 3 from by omega)]
    exact hmiddle

end D5.S3.Combinatorics.VincularStack.VincularStackPatterns
