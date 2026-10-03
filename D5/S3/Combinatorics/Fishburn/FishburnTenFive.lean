/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFive
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFive
   mirror-E: none(waiver:egge-conjecture-ten-five)
   anchors: []
   utility: none
   digest: Ranked insertion histories identify both Fishburn classes with Fibonacci trees. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFiveACount
import D5.S3.Combinatorics.Fishburn.FishburnTenFiveBChildren
import D5.S3.Combinatorics.Fishburn.FishburnTenFiveExtensions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFive

open D5.S3.Combinatorics.Fishburn FishburnDefs FishburnTenFiveBTree
open FishburnTenFiveBChildren FishburnTenFiveExtensions FishburnTenFiveHistory
open FishburnTenFiveBSites FishburnTenFiveBInvariant FishburnTenFivePrepend

set_option maxHeartbeats 3000000 in
theorem result : FishburnDefs.claim105 := by
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
  intro n hn
  refine ⟨FishburnTenFiveACount.A_class_enumeration n hn, ?_⟩
  have hchildren_rule (n : ℕ) (hn : 1 ≤ n) (p : List ℕ)
      (hp : p ∈ avoiders n [[1, 3, 2, 4], [3, 1, 2, 4]])
      (label : Label) (hstate : State n p label) :
      ∃ correspondence : Paths 1 label ≃ {gap : ℕ // gap ≤ p.length ∧
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]]},
        ∀ edge, State (n + 1) (p.insertIdx (correspondence edge).val (n + 1))
          (edgeLabel label edge) := by
    classical
    obtain ⟨start, finish, hstart, hfinish, hfinishlen, hshape, hdecreasing,
      hascent, position, hposition, hat, hlocation⟩ := hstate
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
        avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] :=
      (hshape 0 (by omega)).mpr (Or.inl rfl)
    have hprepend : State (n + 1) ((n + 1) :: p) .L := by
      obtain ⟨newstart, newfinish, _, _, _, hnewshape, _⟩ :=
        all_B_site_invariant (n + 1) (by omega) ((n + 1) :: p)
          (by simpa only [List.insertIdx_zero] using hzero)
      have hnewzero := (hnewshape 0 (by simp)).mpr (Or.inl rfl)
      refine ⟨start + 1, start + 1, by omega, by omega, by simp; omega, ?_, ?_, ?_,
        0, by simp, rfl, by dsimp; omega⟩
      · intro gap hgap
        by_cases hz : gap = 0
        · subst gap
          exact ⟨fun _ => Or.inl rfl, fun _ => hnewzero⟩
        · have hbound : gap - 1 ≤ p.length := by simp only [List.length_cons] at hgap; omega
          have hrule := (prepend_site_rules n p hn hp.1 hp.2.1 (gap - 1) hbound).2
          have hsuccessor : gap - 1 + 1 = gap := by omega
          rw [hsuccessor, hshape (gap - 1) hbound] at hrule
          rw [hrule]
          constructor
          · rintro ⟨hne, hzold | ⟨hlow, hhigh⟩, hdec⟩
            · contradiction
            · have heq : gap - 1 = start := by
                by_contra hnequal
                have ha := hascent start (by omega) (by omega)
                have hd := hdec (start - 1) start (by omega) (by omega)
                omega
              right
              omega
          · rintro (hz | ⟨hlow, hhigh⟩)
            · contradiction
            · have heq : gap - 1 = start := by omega
              refine ⟨by omega, Or.inr ⟨by omega, by omega⟩, ?_⟩
              simpa only [heq] using hdecreasing
      · intro first second hfs hs
        by_cases hfzero : first = 0
        · subst first
          have hsecond : second - 1 < p.length := by omega
          have heq : second = second - 1 + 1 := by omega
          rw [heq, List.getD_cons_succ]
          exact hmax (second - 1) hsecond
        · have hsecond : 0 < second := by omega
          have hf : first = first - 1 + 1 := by omega
          have hh : second = second - 1 + 1 := by omega
          rw [hf, hh, List.getD_cons_succ, List.getD_cons_succ]
          exact hdecreasing (first - 1) (second - 1) (by omega) (by omega)
      · intro edge hlow hhigh
        omega
    have hpositive : ∀ site, start ≤ site → site ≤ finish →
        State (n + 1) (p.insertIdx site (n + 1))
          (if position < site then .M (site - start + 3) else .R (site - start + 2)) := by
      intro site hsstart hsfinish
      have hspos : 0 < site := by omega
      have hsite : site ≤ p.length := by omega
      have hactive := (hshape site hsite).mpr (Or.inr ⟨hsstart, hsfinish⟩)
      have hlength : (p.insertIdx site (n + 1)).length = p.length + 1 :=
        List.length_insertIdx_of_le_length hsite _
      have hupdate := positive_B_site_update n p hp start finish hstart hfinishlen
        hshape hascent site hspos hsite hactive
      let last := if position < site then site + 1 else site
      have hbefore : ∀ index, index < site →
          (p.insertIdx site (n + 1)).getD index 0 = p.getD index 0 := by
        intro index hindex
        rw [List.getD_eq_getElem _ 0 (by omega),
          List.getElem_insertIdx_of_lt hindex, List.getD_eq_getElem p 0 (by omega)]
      have hself : (p.insertIdx site (n + 1)).getD site 0 = n + 1 := by
        rw [List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_insertIdx_self _
      refine ⟨start, last, hstart, by dsimp [last]; split_ifs <;> omega,
        by dsimp [last]; split_ifs <;> omega, ?_, ?_, ?_, site, by omega, hself, ?_⟩
      · intro gap hgap
        rw [hupdate gap hgap, hprevious site hsite]
        dsimp [last]
        split_ifs <;> omega
      · intro first second hfs hs
        rw [hbefore second (by omega), hbefore first (by omega)]
        exact hdecreasing first second hfs hs
      · intro edge hlow hhigh
        by_cases heq : edge = site
        · subst edge
          rw [hbefore (site - 1) (by omega), hself]
          exact hmax (site - 1) (by omega)
        · have hedge : edge < site := by dsimp [last] at hhigh; split_ifs at hhigh <;> omega
          rw [hbefore (edge - 1) (by omega), hbefore edge hedge]
          exact hascent edge hlow (by omega)
      · dsimp [last]
        split_ifs <;> dsimp <;> omega
    let site : Paths 1 label → ℕ := fun edge =>
      if edgeIndex label edge = 0 then 0 else start + edgeIndex label edge - 1
    have hsitevalid : ∀ edge, site edge ≤ p.length ∧
        p.insertIdx (site edge) (n + 1) ∈
          avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
      intro edge
      have hrange : site edge = 0 ∨ start ≤ site edge ∧ site edge ≤ finish := by
        cases label with
        | L => rcases edge with ⟨⟩ | ⟨⟩ <;> simp [site, edgeIndex] <;> omega
        | M sites =>
          rcases edge with (⟨⟩ | ⟨rank, ⟨⟩⟩) | ⟨⟩
          all_goals simp [site, edgeIndex, show sites - 1 ≠ 0 by omega] <;> omega
        | R sites =>
          rcases edge with ⟨⟩ | ⟨rank, ⟨⟩⟩
          all_goals simp [site, edgeIndex] <;> omega
      have hb : site edge ≤ p.length := by omega
      exact ⟨hb, (hshape (site edge) hb).mpr hrange⟩
    let insert : Paths 1 label → {gap : ℕ // gap ≤ p.length ∧
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]]} :=
      fun edge => ⟨site edge, hsitevalid edge⟩
    have hinj : Function.Injective insert := by
      intro first second heq
      have heqsite : site first = site second := congrArg Subtype.val heq
      cases label with
      | L =>
        rcases first with ⟨⟩ | ⟨⟩ <;> rcases second with ⟨⟩ | ⟨⟩
        all_goals first | rfl | (simp [site, edgeIndex] at heqsite; omega)
      | M sites =>
        rcases first with (⟨⟩ | ⟨rank, ⟨⟩⟩) | ⟨⟩ <;>
          rcases second with (⟨⟩ | ⟨other, ⟨⟩⟩) | ⟨⟩
        all_goals simp [site, edgeIndex, show sites - 1 ≠ 0 by omega] at heqsite
        all_goals first
          | rfl
          | (have heqrank : rank = other := Fin.ext (by omega); subst other; rfl)
          | omega
      | R sites =>
        rcases first with ⟨⟩ | ⟨rank, ⟨⟩⟩ <;>
          rcases second with ⟨⟩ | ⟨other, ⟨⟩⟩
        all_goals simp [site, edgeIndex] at heqsite
        all_goals first
          | rfl
          | (have heqrank : rank = other := Fin.ext (by omega); subst other; rfl)
          | omega
    have hsurj : Function.Surjective insert := by
      intro gap
      have hc := (hshape gap.val gap.property.1).mp gap.property.2
      cases label with
      | L =>
        rcases hc with hz | ⟨hlow, hhigh⟩
        · exact ⟨.inl (), Subtype.ext (by simpa [insert, site, edgeIndex] using hz.symm)⟩
        · refine ⟨.inr (), Subtype.ext ?_⟩
          dsimp [insert, site, edgeIndex]
          omega
      | M sites =>
        rcases hc with hz | ⟨hlow, hhigh⟩
        · exact ⟨.inl (.inl ()),
            Subtype.ext (by simpa [insert, site, edgeIndex] using hz.symm)⟩
        · by_cases hlast : gap.val = finish
          · refine ⟨.inr (), Subtype.ext ?_⟩
            change (if sites - 1 = 0 then 0 else start + (sites - 1) - 1) = gap.val
            rw [if_neg (show sites - 1 ≠ 0 by omega)]
            omega
          · let rank : Fin (sites - 2) := ⟨gap.val - start, by omega⟩
            refine ⟨.inl (.inr ⟨rank, ()⟩), Subtype.ext ?_⟩
            dsimp [insert, site, edgeIndex, rank]
            omega
      | R sites =>
        rcases hc with hz | ⟨hlow, hhigh⟩
        · exact ⟨.inl (), Subtype.ext (by simpa [insert, site, edgeIndex] using hz.symm)⟩
        · let rank : Fin (sites - 1) := ⟨gap.val - start, by omega⟩
          refine ⟨.inr ⟨rank, ()⟩, Subtype.ext ?_⟩
          dsimp [insert, site, edgeIndex, rank]
          omega
    refine ⟨Equiv.ofBijective insert ⟨hinj, hsurj⟩, ?_⟩
    intro edge
    change State (n + 1) (p.insertIdx (site edge) (n + 1)) (edgeLabel label edge)
    cases label with
    | L =>
      rcases edge with ⟨⟩ | ⟨⟩
      · simpa [site, edgeIndex, edgeLabel] using hprepend
      · have ha := hpositive start (by omega) (by omega)
        simpa [site, edgeIndex, edgeLabel, show position < start by omega] using ha
    | M sites =>
      rcases edge with (⟨⟩ | ⟨rank, ⟨⟩⟩) | ⟨⟩
      · simpa [site, edgeIndex, edgeLabel] using hprepend
      · have ha := hpositive (start + rank.val) (by omega) (by omega)
        have hnobefore : ¬ position < start + rank.val := by omega
        simpa [site, edgeIndex, edgeLabel, hnobefore, Nat.add_sub_cancel_left] using ha
      · have ha := hpositive finish (by omega) (by omega)
        have heqsite : start + (sites - 1) - 1 = finish := by omega
        have hk : finish - start + 3 = sites + 1 := by omega
        simpa only [site, edgeIndex, if_neg (show sites - 1 ≠ 0 by omega), heqsite,
          edgeLabel, if_pos (show position < finish by omega), hk] using ha
    | R sites =>
      rcases edge with ⟨⟩ | ⟨rank, ⟨⟩⟩
      · simpa [site, edgeIndex, edgeLabel] using hprepend
      · have ha := hpositive (start + rank.val) (by omega) (by omega)
        have hnobefore : ¬ position < start + rank.val := by omega
        simpa [site, edgeIndex, edgeLabel, hnobefore, Nat.add_sub_cancel_left] using ha
  have hvalid : ∀ history : List ℕ,
      LegalHistory [[1, 3, 2, 4], [3, 1, 2, 4]] history →
      replay history ∈ avoiders (history.length + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
    intro history hlegal
    cases history with
    | nil => exact hlegal
    | cons gap earlier =>
      simpa only [replay, List.length_cons, Nat.add_assoc] using hlegal.2.2
  have hpaths : ∀ depth : ℕ, ∀ history : List ℕ,
      LegalHistory [[1, 3, 2, 4], [3, 1, 2, 4]] history → ∀ label : Label,
      State (history.length + 1) (replay history) label →
      Nonempty (Extensions [[1, 3, 2, 4], [3, 1, 2, 4]] depth history ≃ Paths depth label) := by
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
            avoiders (history.length + 2) [[1, 3, 2, 4], [3, 1, 2, 4]]},
          LegalHistory [[1, 3, 2, 4], [3, 1, 2, 4]] (gap.val :: history) := by
        intro gap
        exact ⟨hlegal, gap.property⟩
      have hchildstate : ∀ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) [[1, 3, 2, 4], [3, 1, 2, 4]]},
          State ((gap.val :: history).length + 1) (replay (gap.val :: history))
            (edgeLabel label (children.symm gap)) := by
        intro gap
        simpa only [Equiv.apply_symm_apply] using hchildren' (children.symm gap)
      obtain ⟨decompose, _⟩ := hfirst_extension
        [[1, 3, 2, 4], [3, 1, 2, 4]] depth history
      let descend : (Σ gap : {gap : ℕ // gap ≤ (replay history).length ∧
          (replay history).insertIdx gap (history.length + 2) ∈
            avoiders (history.length + 2) [[1, 3, 2, 4], [3, 1, 2, 4]]},
          Extensions [[1, 3, 2, 4], [3, 1, 2, 4]] depth (gap.val :: history)) ≃
          (Σ edge : Paths 1 label, Paths depth (edgeLabel label edge)) :=
        Equiv.sigmaCongr children.symm (fun gap =>
          Classical.choice (ih (gap.val :: history) (hlegalchild gap)
            (edgeLabel label (children.symm gap)) (hchildstate gap)))
      have hbranches : (Σ edge : Paths 1 label, Paths depth (edgeLabel label edge)) ≃
          Paths (depth + 1) label := by
        cases label with
        | L =>
          refine ⟨(fun branch => match branch with
            | ⟨.inl _, tail⟩ => .inl tail
            | ⟨.inr _, tail⟩ => .inr tail),
            (fun path => match path with
            | .inl tail => ⟨.inl (), tail⟩
            | .inr tail => ⟨.inr (), tail⟩), ?_, ?_⟩
          · rintro ⟨edge, tail⟩
            rcases edge with ⟨⟩ | ⟨⟩ <;> rfl
          · intro path
            cases path <;> rfl
        | M sites =>
          refine ⟨(fun branch => match branch with
            | ⟨.inl (.inl _), tail⟩ => .inl (.inl tail)
            | ⟨.inl (.inr ⟨rank, _⟩), tail⟩ => .inl (.inr ⟨rank, tail⟩)
            | ⟨.inr _, tail⟩ => .inr tail),
            (fun path => match path with
            | .inl (.inl tail) => ⟨.inl (.inl ()), tail⟩
            | .inl (.inr ⟨rank, tail⟩) => ⟨.inl (.inr ⟨rank, ()⟩), tail⟩
            | .inr tail => ⟨.inr (), tail⟩), ?_, ?_⟩
          · rintro ⟨edge, tail⟩
            rcases edge with (⟨⟩ | ⟨rank, ⟨⟩⟩) | ⟨⟩ <;> rfl
          · intro path
            rcases path with (tail | ⟨rank, tail⟩) | tail <;> rfl
        | R sites =>
          refine ⟨(fun branch => match branch with
            | ⟨.inl _, tail⟩ => .inl tail
            | ⟨.inr ⟨rank, _⟩, tail⟩ => .inr ⟨rank, tail⟩),
            (fun path => match path with
            | .inl tail => ⟨.inl (), tail⟩
            | .inr ⟨rank, tail⟩ => ⟨.inr ⟨rank, ()⟩, tail⟩), ?_, ?_⟩
          · rintro ⟨edge, tail⟩
            rcases edge with ⟨⟩ | ⟨rank, ⟨⟩⟩ <;> rfl
          · intro path
            rcases path with tail | ⟨rank, tail⟩ <;> rfl
      exact ⟨decompose.trans (descend.trans hbranches)⟩
  have hroot : [1] ∈ avoiders 1 [[1, 3, 2, 4], [3, 1, 2, 4]] := by
    refine ⟨by decide, ?_, ?_⟩
    · intro before later hfar hbound
      change later < 1 at hbound
      omega
    · intro pattern hpattern hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by simpa using hpattern
      rcases hc with rfl | rfl <;>
        obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
        have hlen := hsub.length_le <;>
        simp only [List.length_map, List.length_cons, List.length_nil] at hlen <;> omega
  have hrootstate : State 1 [1] .L := by
    refine ⟨1, 1, by omega, by omega, by simp, ?_, ?_, ?_, 0, by simp, rfl, by dsimp; omega⟩
    · intro gap hgap
      change gap ≤ 1 at hgap
      have hc : gap = 0 ∨ gap = 1 := by omega
      constructor
      · intro _
        omega
      · intro _
        rcases hc with rfl | rfl <;> refine ⟨by decide, ?_, ?_⟩
        all_goals first
          | (intro before later hfar hbound; change later < 2 at hbound; omega)
          | (intro pattern hpattern hocc
             have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
               simpa using hpattern
             rcases hc with rfl | rfl <;>
               obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
               have hlen := hsub.length_le <;>
               simp only [List.length_map, List.length_cons, List.length_nil,
                 List.insertIdx_zero, List.insertIdx_succ_cons] at hlen <;> omega)
    · intro first second hfs hs
      omega
    · intro edge hlow hhigh
      omega
  obtain ⟨paths⟩ := hpaths (n - 1) [] hroot .L hrootstate
  let histories : {history : List ℕ // history.length = n - 1 ∧
      LegalHistory [[1, 3, 2, 4], [3, 1, 2, 4]] history} ≃
      Extensions [[1, 3, 2, 4], [3, 1, 2, 4]] (n - 1) [] :=
    ⟨(fun history => ⟨history.val, by
      refine ⟨by simpa using history.property.1, history.property.2, ?_⟩
      simp only [← history.property.1, List.drop_length]⟩),
      (fun later => ⟨later.val, by
        exact ⟨by simpa using later.property.1, later.property.2.1⟩⟩),
      fun _ => rfl, fun _ => rfl⟩
  obtain ⟨permutations, _⟩ := maximum_history_equivalence
    [[1, 3, 2, 4], [3, 1, 2, 4]] (n - 1)
  have hsize : n - 1 + 1 = n := by omega
  have hcard := Nat.card_congr (permutations.symm.trans (histories.trans paths))
  rw [Nat.card_coe_set_eq, B_path_enumeration] at hcard
  simpa only [hsize, show 2 * (n - 1) + 1 = 2 * n - 1 by omega] using hcard

end D5.S3.Combinatorics.Fishburn.FishburnTenFive
