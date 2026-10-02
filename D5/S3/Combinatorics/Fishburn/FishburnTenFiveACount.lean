/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveACount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveACount
   mirror-E: none(waiver:a-class-ranked-history-bijection)
   anchors: []
   utility: none
   digest: Recursively identify legal A histories with ranked paths and count every A class. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFiveAChildren
import D5.S3.Combinatorics.Fishburn.FishburnTenFiveExtensions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveACount

open D5.S3.Combinatorics.Fishburn FishburnDefs FishburnTenFiveATree
open FishburnTenFiveAChildren FishburnTenFiveExtensions FishburnTenFiveHistory
open FishburnTenFiveASites FishburnTenFiveAInvariant FishburnTenFivePrepend

set_option maxHeartbeats 2400000 in
theorem A_class_enumeration (n : ℕ) (hn : 1 ≤ n) :
    (avoiders n [[1, 3, 2, 4], [1, 4, 2, 3]]).ncard = Nat.fib (2 * n - 1) := by
  classical
  letI : ∀ label, Fintype (Paths 1 label) := by
    intro label
    cases label <;> dsimp [Paths] <;> infer_instance
  have hfirst_extension (patterns : List (List ℕ)) (depth : ℕ)
      (history : List ℕ) :
      ∃ correspondence : Extensions patterns (depth + 1) history ≃
        (Σ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) patterns},
          Extensions patterns depth (gap.val :: history)),
        ∀ later, (correspondence later).2.val = later.val := by
    have hdrop : ∀ count : ℕ, ∀ later : List ℕ,
        LegalHistory patterns later → LegalHistory patterns (later.drop count) := by
      intro count
      induction count with
      | zero => intro later hlegal; simpa using hlegal
      | succ count ih =>
        intro later hlegal
        cases later with
        | nil => simpa using hlegal
        | cons gap earlier =>
          simpa only [List.drop_succ_cons] using ih earlier hlegal.1
    have hsplit : ∀ later : Extensions patterns (depth + 1) history,
        ∃ gap : ℕ, later.val.drop depth = gap :: history ∧
          gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) patterns := by
      intro later
      have hlength : (later.val.drop depth).length = history.length + 1 := by
        rw [List.length_drop, later.property.1]
        omega
      have htail : (later.val.drop depth).drop 1 = history := by
        rw [List.drop_drop]
        simpa only [Nat.add_comm] using later.property.2.2
      have hlegal := hdrop depth later.val later.property.2.1
      cases heq : later.val.drop depth with
      | nil => rw [heq] at hlength; simp at hlength
      | cons gap earlier =>
        have hear : earlier = history := by
          simpa only [heq, List.drop_one, List.tail_cons] using htail
        subst earlier
        rw [heq] at hlegal
        exact ⟨gap, rfl, hlegal.2⟩
    let split : Extensions patterns (depth + 1) history →
        (Σ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) patterns},
          Extensions patterns depth (gap.val :: history)) := fun later =>
      let gap := Classical.choose (hsplit later)
      let spec := Classical.choose_spec (hsplit later)
      ⟨⟨gap, spec.2⟩, ⟨later.val, by
        refine ⟨?_, later.property.2.1, spec.1⟩
        simp only [List.length_cons]
        have hl := later.property.1
        omega⟩⟩
    let join : (Σ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) patterns},
          Extensions patterns depth (gap.val :: history)) →
        Extensions patterns (depth + 1) history := fun branch =>
      ⟨branch.2.val, by
        refine ⟨?_, branch.2.property.2.1, ?_⟩
        · have hl := branch.2.property.1
          simp only [List.length_cons] at hl
          omega
        · rw [← List.drop_drop,
            branch.2.property.2.2]
          rfl⟩
    refine ⟨⟨split, join, ?_, ?_⟩, fun _ => rfl⟩
    · intro later
      apply Subtype.ext
      rfl
    · intro branch
      have hgap : (split (join branch)).1 = branch.1 := by
        apply Subtype.ext
        have hs := Classical.choose_spec (hsplit (join branch))
        have hd : (join branch).val.drop depth = branch.1.val :: history :=
          branch.2.property.2.2
        exact (List.cons.inj (hs.1.symm.trans hd)).1
      apply Sigma.ext hgap
      apply (Subtype.heq_iff_coe_eq (by intro later; rw [hgap])).mpr
      rfl
  have hchildren_rule (n : ℕ) (hn : 1 ≤ n) (p : List ℕ)
      (hp : p ∈ avoiders n [[1, 3, 2, 4], [1, 4, 2, 3]])
      (label : Label) (hstate : State n p label) :
      ∃ correspondence : Paths 1 label ≃ {gap : ℕ // gap ≤ p.length ∧
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]]},
        ∀ edge, State (n + 1) (p.insertIdx (correspondence edge).val (n + 1))
          (edgeLabel label edge) := by
    classical
    obtain ⟨start, hstart, hstartlen, hshape, hascent, position, hposition,
      hat, hlocation⟩ := hstate
    have hnodup : p.Nodup := hp.1.nodup_iff.mpr (List.nodup_range' 1)
    have hmax : ∀ index, index < p.length → p.getD index 0 < n + 1 := by
      intro index hindex
      rw [List.getD_eq_getElem p 0 hindex]
      have hm := hp.1.mem_iff.mp (List.getElem_mem hindex)
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨offset, hoffset, heq⟩ := hm
      omega
    have hprevious : ∀ site, site ≤ p.length →
        ((∃ earlier < site, p.getD earlier 0 = n) ↔ position < site) := by
      intro site hsite
      constructor
      · rintro ⟨earlier, hear, hvalue⟩
        have heq : earlier = position :=
          (List.getD_inj (by omega) hposition hnodup).mp (hvalue.trans hat.symm)
        omega
      · intro hbefore
        exact ⟨position, hbefore, hat⟩
    have hzero : p.insertIdx 0 (n + 1) ∈
        avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] :=
      (hshape 0 (by omega)).mpr (Or.inl rfl)
    have hprepend : State (n + 1) ((n + 1) :: p)
        (if label = .P ∨ label = .Q then .Q else .D) := by
      obtain ⟨newstart, _, _, newthree, hnewshape, _⟩ :=
        all_A_site_invariant (n + 1) (by omega) ((n + 1) :: p)
          (by simpa only [List.insertIdx_zero] using hzero)
      have hnewzero := (hnewshape 0 (by simp)).mpr (Or.inl rfl)
      refine ⟨start + 1, by omega, by simp; omega, ?_, ?_, 0, by simp, rfl, ?_⟩
      · intro gap hgap
        by_cases hz : gap = 0
        · subst gap
          exact ⟨fun _ => Or.inl rfl, fun _ => hnewzero⟩
        · have hbound : gap - 1 ≤ p.length := by simp only [List.length_cons] at hgap; omega
          have hrule := (prepend_site_rules n p hn hp.1 hp.2.1 (gap - 1) hbound).1
          have hsuccessor : gap - 1 + 1 = gap := by omega
          rw [hsuccessor, hshape (gap - 1) hbound] at hrule
          rw [hrule]
          split_ifs with ht <;> simp only [ht, reduceCtorEq,
            or_false, false_or, true_or, true_and, false_and] <;> omega
      · intro hthree
        have hparentthree : label = .P ∨ label = .Q := by
          split_ifs at hthree with hthreeparent
          · exact hthreeparent
          · simp at hthree
        obtain ⟨hsmall, hsep⟩ := hascent hparentthree
        refine ⟨by simp; omega, ?_⟩
        rw [Nat.add_sub_cancel, List.getD_cons_succ]
        have hshift : ((n + 1) :: p).getD start 0 = p.getD (start - 1) 0 := by
          conv_lhs => rw [show start = start - 1 + 1 by omega, List.getD_cons_succ]
        rwa [hshift]
      · split_ifs <;> dsimp <;> omega
    have hpositive : ∀ site, 0 < site → site ≤ p.length →
        p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] →
        State (n + 1) (p.insertIdx site (n + 1))
          (if position < site then .P else .E) := by
      intro site hspos hsite hactive
      have hlength : (p.insertIdx site (n + 1)).length = p.length + 1 :=
        List.length_insertIdx_of_le_length hsite _
      have hupdate := positive_A_site_update n p hp start hstart
        (label = .P ∨ label = .Q) hshape hascent site hspos hsite hactive
      refine ⟨site, by omega, by omega, ?_, ?_, site, by omega, ?_, ?_⟩
      · intro gap hgap
        rw [hupdate gap hgap, hprevious site hsite]
        split_ifs <;> simp <;> omega
      · intro _
        refine ⟨by omega, ?_⟩
        have hbefore : (p.insertIdx site (n + 1)).getD (site - 1) 0 =
            p.getD (site - 1) 0 := by
          rw [List.getD_eq_getElem _ 0 (by omega),
            List.getElem_insertIdx_of_lt (by omega),
            List.getD_eq_getElem p 0 (by omega)]
        have hself : (p.insertIdx site (n + 1)).getD site 0 = n + 1 := by
          rw [List.getD_eq_getElem _ 0 (by omega)]
          exact List.getElem_insertIdx_self _
        rw [hbefore, hself]
        exact hmax (site - 1) (by omega)
      · rw [List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_insertIdx_self _
      · split_ifs <;> dsimp <;> omega
    let site : Paths 1 label → ℕ := fun edge =>
      if edgeIndex label edge = 0 then 0 else start + edgeIndex label edge - 1
    have hsitevalid : ∀ edge, site edge ≤ p.length ∧
        p.insertIdx (site edge) (n + 1) ∈
          avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
      intro edge
      cases label <;> cases edge with
      | inl first =>
        simpa [site, edgeIndex] using (And.intro (show 0 ≤ p.length by omega) hzero)
      | inr rest =>
        solve
        | (dsimp [site, edgeIndex]
           exact ⟨hstartlen, (hshape start hstartlen).mpr (Or.inr (Or.inl rfl))⟩)
        | (cases rest with
           | inl second =>
             dsimp [site, edgeIndex]
             exact ⟨hstartlen, (hshape start hstartlen).mpr (Or.inr (Or.inl rfl))⟩
           | inr third =>
             have ha := (hascent (by simp)).1
             have hb : start + 1 ≤ p.length := by omega
             refine ⟨?_, ?_⟩
             · dsimp [site, edgeIndex]; omega
             · have heq : site (.inr (.inr third)) = start + 1 := by
                 dsimp [site, edgeIndex] <;> omega
               rw [heq]
               exact (hshape (start + 1) hb).mpr (Or.inr (Or.inr ⟨by simp, rfl⟩)))
    let insert : Paths 1 label → {gap : ℕ // gap ≤ p.length ∧
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]]} :=
      fun edge => ⟨site edge, hsitevalid edge⟩
    have hinj : Function.Injective insert := by
      intro first second heq
      have heqsite : site first = site second := congrArg Subtype.val heq
      cases label <;> fin_cases first <;> fin_cases second
      all_goals simp [site, edgeIndex] at heqsite ⊢
      all_goals first | rfl | omega
    have hsurj : Function.Surjective insert := by
      intro gap
      have hc := (hshape gap.val gap.property.1).mp gap.property.2
      cases label <;> rcases hc with hz | hs | ⟨hthree, hs⟩
      all_goals solve
        | (refine ⟨.inl (), Subtype.ext ?_⟩; simpa [insert, site, edgeIndex] using hz.symm)
        | (refine ⟨.inr (), Subtype.ext ?_⟩; simpa [insert, site, edgeIndex] using hs.symm)
        | (simp at hthree)
        | (refine ⟨.inr (.inl ()), Subtype.ext ?_⟩
           simpa [insert, site, edgeIndex] using hs.symm)
        | (refine ⟨.inr (.inr ()), Subtype.ext ?_⟩
           dsimp [insert, site, edgeIndex]; omega)
    refine ⟨Equiv.ofBijective insert ⟨hinj, hsurj⟩, ?_⟩
    · intro edge
      change State (n + 1) (p.insertIdx (site edge) (n + 1)) (edgeLabel label edge)
      cases label <;> cases edge with
      | inl first => simpa [site, edgeIndex, edgeLabel] using hprepend
      | inr rest =>
        solve
        | (have ha := hpositive start (by omega) hstartlen
             ((hshape start hstartlen).mpr (Or.inr (Or.inl rfl)))
           simpa [site, edgeIndex, edgeLabel, show position < start by omega] using ha)
        | (have ha := hpositive start (by omega) hstartlen
             ((hshape start hstartlen).mpr (Or.inr (Or.inl rfl)))
           simpa [site, edgeIndex, edgeLabel, show ¬ position < start by omega] using ha)
        | (cases rest with
           | inl second =>
             have ha := hpositive start (by omega) hstartlen
               ((hshape start hstartlen).mpr (Or.inr (Or.inl rfl)))
             solve
             | simpa [site, edgeIndex, edgeLabel, show ¬ position < start by omega] using ha
             | simpa [site, edgeIndex, edgeLabel, show position < start by omega] using ha
           | inr third =>
             have hb : start + 1 ≤ p.length := by have ha := (hascent (by simp)).1; omega
             have ha := hpositive (start + 1) (by omega) hb
               ((hshape (start + 1) hb).mpr (Or.inr (Or.inr ⟨by simp, rfl⟩)))
             have heq : start + 2 - 1 = start + 1 := by omega
             simpa [site, edgeIndex, edgeLabel, heq, show position < start + 1 by omega]
               using ha)
  have hvalid : ∀ history : List ℕ,
      LegalHistory [[1, 3, 2, 4], [1, 4, 2, 3]] history →
      replay history ∈ avoiders (history.length + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
    intro history hlegal
    cases history with
    | nil => exact hlegal
    | cons gap earlier =>
      simpa only [replay, List.length_cons, Nat.add_assoc] using hlegal.2.2
  have hpaths : ∀ depth : ℕ, ∀ history : List ℕ,
      LegalHistory [[1, 3, 2, 4], [1, 4, 2, 3]] history → ∀ label : Label,
      State (history.length + 1) (replay history) label →
      Nonempty (Extensions [[1, 3, 2, 4], [1, 4, 2, 3]] depth history ≃ Paths depth label) := by
    intro depth
    induction depth with
    | zero =>
      intro history hlegal label _
      refine ⟨⟨fun _ => (), fun _ => ⟨history, by simp [hlegal]⟩, ?_, ?_⟩⟩
      · intro later
        apply Subtype.ext
        simpa only [List.drop_zero] using later.property.2.2.symm
      · intro path
        cases path
        rfl
    | succ depth ih =>
      intro history hlegal label hstate
      obtain ⟨children, hchildren⟩ := hchildren_rule (history.length + 1) (by omega)
        (replay history) (hvalid history hlegal) label hstate
      have hchildren' : ∀ edge, State (((children edge).val :: history).length + 1)
          (replay ((children edge).val :: history)) (edgeLabel label edge) := by
        intro edge
        simpa only [replay, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using hchildren edge
      have hlegalchild : ∀ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) [[1, 3, 2, 4], [1, 4, 2, 3]]},
          LegalHistory [[1, 3, 2, 4], [1, 4, 2, 3]] (gap.val :: history) := by
        intro gap
        exact ⟨hlegal, gap.property⟩
      have hchildstate : ∀ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) [[1, 3, 2, 4], [1, 4, 2, 3]]},
          State ((gap.val :: history).length + 1) (replay (gap.val :: history))
            (edgeLabel label (children.symm gap)) := by
        intro gap
        simpa only [Equiv.apply_symm_apply] using hchildren' (children.symm gap)
      obtain ⟨decompose, _⟩ := hfirst_extension
        [[1, 3, 2, 4], [1, 4, 2, 3]] depth history
      let descend : (Σ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) [[1, 3, 2, 4], [1, 4, 2, 3]]},
          Extensions [[1, 3, 2, 4], [1, 4, 2, 3]] depth (gap.val :: history)) ≃
          (Σ edge : Paths 1 label, Paths depth (edgeLabel label edge)) :=
        Equiv.sigmaCongr children.symm (fun gap =>
        Classical.choice (ih (gap.val :: history) (hlegalchild gap)
          (edgeLabel label (children.symm gap)) (hchildstate gap)))
      have hbranches : (Σ edge : Paths 1 label, Paths depth (edgeLabel label edge)) ≃
          Paths (depth + 1) label := by
        cases label with
        | D =>
          refine ⟨(fun branch => match branch with
            | ⟨.inl _, tail⟩ => .inl tail
            | ⟨.inr _, tail⟩ => .inr tail),
            (fun path => match path with
            | .inl tail => ⟨.inl (), tail⟩
            | .inr tail => ⟨.inr (), tail⟩), ?_, ?_⟩
          · rintro ⟨edge, tail⟩
            cases edge <;> rename_i unit <;> cases unit <;> rfl
          · intro path
            cases path <;> rfl
        | E =>
          refine ⟨(fun branch => match branch with
            | ⟨.inl _, tail⟩ => .inl tail
            | ⟨.inr _, tail⟩ => .inr tail),
            (fun path => match path with
            | .inl tail => ⟨.inl (), tail⟩
            | .inr tail => ⟨.inr (), tail⟩), ?_, ?_⟩
          · rintro ⟨edge, tail⟩
            cases edge <;> rename_i unit <;> cases unit <;> rfl
          · intro path
            cases path <;> rfl
        | P =>
          refine ⟨(fun branch => match branch with
            | ⟨.inl _, tail⟩ => .inl tail
            | ⟨.inr (.inl _), tail⟩ => .inr (.inl tail)
            | ⟨.inr (.inr _), tail⟩ => .inr (.inr tail)),
            (fun path => match path with
            | .inl tail => ⟨.inl (), tail⟩
            | .inr (.inl tail) => ⟨.inr (.inl ()), tail⟩
            | .inr (.inr tail) => ⟨.inr (.inr ()), tail⟩), ?_, ?_⟩
          · rintro ⟨edge, tail⟩
            cases edge with
            | inl unit => cases unit; rfl
            | inr rest => cases rest <;> rename_i unit <;> cases unit <;> rfl
          · intro path
            cases path with
            | inl tail => rfl
            | inr rest => cases rest <;> rfl
        | Q =>
          refine ⟨(fun branch => match branch with
            | ⟨.inl _, tail⟩ => .inl tail
            | ⟨.inr (.inl _), tail⟩ => .inr (.inl tail)
            | ⟨.inr (.inr _), tail⟩ => .inr (.inr tail)),
            (fun path => match path with
            | .inl tail => ⟨.inl (), tail⟩
            | .inr (.inl tail) => ⟨.inr (.inl ()), tail⟩
            | .inr (.inr tail) => ⟨.inr (.inr ()), tail⟩), ?_, ?_⟩
          · rintro ⟨edge, tail⟩
            cases edge with
            | inl unit => cases unit; rfl
            | inr rest => cases rest <;> rename_i unit <;> cases unit <;> rfl
          · intro path
            cases path with
            | inl tail => rfl
            | inr rest => cases rest <;> rfl
      exact ⟨decompose.trans (descend.trans hbranches)⟩
  have hroot : [1] ∈ avoiders 1 [[1, 3, 2, 4], [1, 4, 2, 3]] := by
    refine ⟨by decide, ?_, ?_⟩
    · intro before later hfar hbound
      change later < 1 at hbound
      omega
    · intro pattern hpattern hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by simpa using hpattern
      rcases hc with rfl | rfl <;>
        obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
        have hlen := hsub.length_le <;>
        simp only [List.length_map, List.length_cons, List.length_nil] at hlen <;> omega
  have hrootstate : State 1 [1] .D := by
    refine ⟨1, by omega, by simp, ?_, by simp, 0, by simp, rfl, by omega⟩
    intro gap hgap
    change gap ≤ 1 at hgap
    have hc : gap = 0 ∨ gap = 1 := by omega
    constructor
    · intro _
      simpa using hc
    · intro _
      rcases hc with rfl | rfl <;> refine ⟨by decide, ?_, ?_⟩
      all_goals first
        | (intro before later hfar hbound; change later < 2 at hbound; omega)
        | (intro pattern hpattern hocc
           have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
             simpa using hpattern
           rcases hc with rfl | rfl <;>
             obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
             have hlen := hsub.length_le <;>
             simp only [List.length_map, List.length_cons, List.length_nil,
               List.insertIdx_zero, List.insertIdx_succ_cons] at hlen <;> omega)
  obtain ⟨paths⟩ := hpaths (n - 1) [] hroot .D hrootstate
  let histories : {history : List ℕ // history.length = n - 1 ∧
      LegalHistory [[1, 3, 2, 4], [1, 4, 2, 3]] history} ≃
      Extensions [[1, 3, 2, 4], [1, 4, 2, 3]] (n - 1) [] :=
    ⟨(fun history => ⟨history.val, by
      refine ⟨by simpa using history.property.1, history.property.2, ?_⟩
      simp only [← history.property.1, List.drop_length]⟩),
      (fun later => ⟨later.val, by
        exact ⟨by simpa using later.property.1, later.property.2.1⟩⟩),
      fun _ => rfl, fun _ => rfl⟩
  obtain ⟨permutations, _⟩ := maximum_history_equivalence
    [[1, 3, 2, 4], [1, 4, 2, 3]] (n - 1)
  have hsize : n - 1 + 1 = n := by omega
  have hcard := Nat.card_congr (permutations.symm.trans (histories.trans paths))
  rw [Nat.card_coe_set_eq, A_path_enumeration] at hcard
  simpa only [hsize, show 2 * (n - 1) + 1 = 2 * n - 1 by omega] using hcard

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveACount
