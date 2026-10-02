/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourCLabels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourCLabels
   mirror-E: none(waiver:c-labelled-active-edge-bijection)
   anchors: []
   utility: none
   digest: Weighted maximum-deletion bijections prove the arbitrary-size C count. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFourCInvariant
import D5.S3.Combinatorics.Fishburn.FishburnTenFourCTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourCLabels

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicPatterns FishburnBasicPrefixes
open FishburnTenFourCInvariant FishburnTenFourCTree

def Valley (p : List ℕ) : Prop :=
  ∃ one, one < p.length ∧ p.getD one 0 = 1 ∧
    ∀ earlier later, one < earlier → earlier < later → later < p.length →
      p.getD later 0 < p.getD earlier 0

noncomputable def label (n : ℕ) (p : List ℕ) : Label := by
  classical
  exact if p.getD 0 0 = n then if Valley p then .T else .V
    else if Valley p then .S else .U

theorem C_count (size : ℕ) (hsize : 1 ≤ size) :
    (avoiders size [[1, 4, 2, 3], [3, 1, 2, 4]]).ncard =
      (size - 1) * 2 ^ (size - 2) + 1 := by
  let rec pathsFintype (depth : ℕ) (mark : Label) : Fintype (Paths depth mark) :=
    match depth, mark with
    | 0, _ => inferInstanceAs (Fintype Unit)
    | depth + 1, mark =>
      letI : ∀ mark, Fintype (Paths depth mark) := pathsFintype depth
      by cases mark <;> dsimp [Paths] <;> infer_instance
  letI (depth : ℕ) (mark : Label) : Fintype (Paths depth mark) := pathsFintype depth mark
  have hpathcount (depth : ℕ) :
      Nat.card (Paths depth .T) = depth * 2 ^ (depth - 1) + 1 := by
    have hcounts : ∀ count,
        Nat.card (Paths (count + 1) .T) = (count + 1) * 2 ^ count + 1 ∧
        Nat.card (Paths (count + 1) .S) = (count + 3) * 2 ^ count ∧
        Nat.card (Paths (count + 1) .U) + 1 = 2 ^ (count + 2) ∧
        Nat.card (Paths (count + 1) .V) = 1 := by
      intro count
      induction count with
      | zero => simp [Paths, Nat.card_eq_fintype_card]
      | succ count ih =>
        have hT : Nat.card (Paths (count + 2) .T) =
            Nat.card (Paths (count + 1) .T) + Nat.card (Paths (count + 1) .S) := by
          simp only [Paths, Nat.card_sum]
        have hS : Nat.card (Paths (count + 2) .S) =
            Nat.card (Paths (count + 1) .T) + Nat.card (Paths (count + 1) .S) +
              Nat.card (Paths (count + 1) .U) := by
          simp only [Paths, Nat.card_sum]
        have hU : Nat.card (Paths (count + 2) .U) =
            Nat.card (Paths (count + 1) .V) + Nat.card (Paths (count + 1) .U) +
              Nat.card (Paths (count + 1) .U) := by
          simp only [Paths, Nat.card_sum]
        have hV : Nat.card (Paths (count + 2) .V) = Nat.card (Paths (count + 1) .V) := rfl
        have hp : 2 ^ (count + 2) = 4 * 2 ^ count := by
          rw [Nat.pow_add]
          ring
        have hpnext : 2 ^ (count + 1 + 2) = 2 * 2 ^ (count + 2) := by
          rw [show count + 1 + 2 = count + 2 + 1 by omega, Nat.pow_succ]
          ring
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hT, ih.1, ih.2.1, Nat.pow_succ]
          ring
        · rw [hS, ih.1, ih.2.1, Nat.pow_succ]
          have hu := ih.2.2.1
          rw [hp] at hu
          nlinarith
        · rw [hU, ih.2.2.2, hpnext]
          omega
        · rw [hV, ih.2.2.2]
    cases depth with
    | zero => simp [Paths, Nat.card_eq_fintype_card]
    | succ count => simpa only [Nat.add_sub_cancel] using (hcounts count).1
  have maximum_insertion_valley_iff (n : ℕ) (p : List ℕ)
      (hperm : p.Perm (List.range' 1 n)) (one site : ℕ)
      (hone : one < site) (hsite : site ≤ p.length) :
      (∀ earlier later, one < earlier → earlier < later →
        later < (p.insertIdx site (n + 1)).length →
          (p.insertIdx site (n + 1)).getD later 0 <
            (p.insertIdx site (n + 1)).getD earlier 0) ↔
        (∀ earlier later, one < earlier → earlier < later → later < p.length →
          p.getD later 0 < p.getD earlier 0) ∧ site = one + 1 := by
    let child := p.insertIdx site (n + 1)
    let lift := fun index : ℕ => if index < site then index else index + 1
    have hlen : child.length = p.length + 1 := List.length_insertIdx_of_le_length hsite _
    have hbound (index : ℕ) (hi : index < p.length) : p.getD index 0 < n + 1 := by
      have hm : p.getD index 0 ∈ p := by
        rw [List.getD_eq_getElem p 0 hi]
        exact List.getElem_mem hi
      have hrange := hperm.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, heq⟩ := hrange
      omega
    have hbefore (index : ℕ) (hi : index < site) : child.getD index 0 = p.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hafter (index : ℕ) (hi : site < index) (hb : index < child.length) :
        child.getD index 0 = p.getD (index - 1) 0 := by
      rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hliftbound (index : ℕ) (hi : index < p.length) : lift index < child.length := by
      dsimp [lift]
      split_ifs <;> omega
    have hliftentry (index : ℕ) (hi : index < p.length) :
        child.getD (lift index) 0 = p.getD index 0 := by
      dsimp [lift]
      split_ifs with hlt
      · exact hbefore index hlt
      · simpa only [Nat.add_sub_cancel] using hafter (index + 1) (by omega) (by omega)
    change (∀ earlier later, one < earlier → earlier < later → later < child.length →
      child.getD later 0 < child.getD earlier 0) ↔ _
    constructor
    · intro hchild
      constructor
      · intro earlier later he hl hb
        have hlifte : one < lift earlier := by dsimp [lift]; split_ifs <;> omega
        have hliftorder : lift earlier < lift later := by dsimp [lift]; split_ifs <;> omega
        have hh := hchild (lift earlier) (lift later) hlifte hliftorder (hliftbound later hb)
        rwa [hliftentry later hb, hliftentry earlier (by omega)] at hh
      · by_contra hnot
        have hlt : one + 1 < site := by omega
        have hh := hchild (one + 1) site (by omega) hlt (by omega)
        rw [hat, hbefore (one + 1) hlt] at hh
        have hb := hbound (one + 1) (by omega)
        omega
    · rintro ⟨hparent, hsiteone⟩ earlier later he hl hb
      have hearliersite : site ≤ earlier := by omega
      by_cases heq : earlier = site
      · subst earlier
        rw [hat, hafter later (by omega) hb]
        exact hbound (later - 1) (by omega)
      · rw [hafter later (by omega) hb, hafter earlier (by omega) (by omega)]
        exact hparent (earlier - 1) (later - 1) (by omega) (by omega) (by omega)
  classical
  have C_labelled_edges (n : ℕ) (p : List ℕ) (hn : 1 ≤ n)
      (hparent : p ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]) :
      ∃ correspondence : Paths 1 (label n p) ≃ {cut : ℕ // cut ≤ p.length ∧
        p.insertIdx cut (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]},
        ∀ edge, label (n + 1) (p.insertIdx (correspondence edge).val (n + 1)) =
          nextLabel (label n p) edge := by
    classical
    have hlen : p.length = n := by simpa using hparent.1.length_eq
    have hmax (value : ℕ) (hm : value ∈ p) : value < n + 1 := by
      have hrange := hparent.1.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, heq⟩ := hrange
      omega
    have hbound (index : ℕ) (hi : index < p.length) : p.getD index 0 < n + 1 := by
      rw [List.getD_eq_getElem p 0 hi]
      exact hmax _ (List.getElem_mem hi)
    have hvalleyat (size : ℕ) (word : List ℕ)
        (hperm : word.Perm (List.range' 1 size)) (one : ℕ)
        (hb : one < word.length) (hv : word.getD one 0 = 1) :
        Valley word ↔ ∀ earlier later, one < earlier → earlier < later →
          later < word.length →
          word.getD later 0 < word.getD earlier 0 := by
      constructor
      · rintro ⟨other, hob, hov, hdec⟩
        have heq := (List.getD_inj hob hb (hperm.nodup_iff.mpr (List.nodup_range' 1))).mp
          (hov.trans hv.symm)
        subst other
        exact hdec
      · intro hdec
        exact ⟨one, hb, hv, hdec⟩
    have hfront : p.insertIdx 0 (n + 1) ∈
        avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] := by
      refine ⟨?_, ?_, ?_⟩
      · apply (List.perm_insertIdx (n + 1) p (by omega)).trans
        apply (hparent.1.cons (n + 1)).trans
        rw [List.range'_concat]
        simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
      · apply (isFishburn_insertIdx_max_iff p (n + 1) 0 (by omega) hmax).mpr
        exact ⟨hparent.2.1, by intro before later heq; omega⟩
      · have htests := maximum_pattern_tests n p hparent.1 0 (by omega)
        intro pattern hm hocc
        have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := by simpa using hm
        rcases hc with rfl | rfl
        · exact hparent.2.2 _ hm (by simpa using htests.2.2.mp hocc)
        · exact hparent.2.2 _ hm (by simpa using htests.2.1.mp hocc)
    obtain ⟨one, honebound, hone, hcase⟩ := all_C_site_invariant n hn p hparent
    have hvalleyparent := hvalleyat n p hparent.1 one honebound hone
    have hfrontlabel : label (n + 1) (p.insertIdx 0 (n + 1)) =
        if Valley p then .T else .V := by
      let child := (n + 1) :: p
      have honechild : child.getD (one + 1) 0 = 1 := by
        simpa only [child, List.getD_cons_succ] using hone
      have hvalleychild := hvalleyat (n + 1) child hfront.1 (one + 1)
        (by simp only [child, List.length_cons]; omega) honechild
      have hsame : Valley child ↔ Valley p := by
        rw [hvalleychild, hvalleyparent]
        constructor
        · intro hv earlier later he hl hb
          have hh := hv (earlier + 1) (later + 1) (by omega) (by omega)
            (by simp only [child, List.length_cons]; omega)
          simpa only [child, List.getD_cons_succ] using hh
        · intro hv earlier later he hl hb
          have hget (index : ℕ) (hi : 0 < index) :
              child.getD index 0 = p.getD (index - 1) 0 := by
            obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : index ≠ 0)
            simp [child]
          rw [hget later (by omega), hget earlier (by omega)]
          exact hv (earlier - 1) (later - 1) (by omega) (by omega)
            (by simp only [child, List.length_cons] at hb; omega)
      change label (n + 1) child = _
      unfold label
      have hhead : child.getD 0 0 = n + 1 := rfl
      rw [if_pos hhead, hsame]
    have hpositiveone (cut : ℕ) (hp : 0 < cut) (hb : cut ≤ p.length)
        (ha : p.insertIdx cut (n + 1) ∈
          avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]) : one < cut := by
      have heligible := (isFishburn_insertIdx_max_iff p (n + 1) cut hb hmax).mp ha.2.1 |>.2
      have hm := (eligible_prefix_structure n p hparent.1 hparent.2.1 cut hb hp heligible).1
      obtain ⟨index, hib, hiv⟩ := List.mem_iff_getElem.mp hm
      have hindexbound : index < p.length := by simp only [List.length_take] at hib; omega
      have hindexvalue : p.getD index 0 = 1 := by
        rw [List.getD_eq_getElem p 0 hindexbound]
        simpa only [List.getElem_take] using hiv
      have hi := (List.getD_inj hindexbound honebound
        (hparent.1.nodup_iff.mpr (List.nodup_range' 1))).mp (hindexvalue.trans hone.symm)
      simp only [List.length_take] at hib
      omega
    have hpositivelabel (cut : ℕ) (hp : 0 < cut) (hb : cut ≤ p.length)
        (ha : p.insertIdx cut (n + 1) ∈
          avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]) :
        label (n + 1) (p.insertIdx cut (n + 1)) =
          if Valley p ∧ cut = one + 1 then .S else .U := by
      let child := p.insertIdx cut (n + 1)
      have honecut := hpositiveone cut hp hb ha
      have hchildlen : child.length = p.length + 1 := List.length_insertIdx_of_le_length hb _
      have hbefore (index : ℕ) (hi : index < cut) :
          child.getD index 0 = p.getD index 0 := by
        rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
          List.getD_eq_getElem p 0 (by omega)]
      have hchildone : child.getD one 0 = 1 := by rw [hbefore one honecut, hone]
      have hnotfirst : child.getD 0 0 ≠ n + 1 := by
        rw [hbefore 0 hp]
        have hv := hbound 0 (by omega)
        omega
      have hchildvalley := hvalleyat (n + 1) child ha.1 one (by omega) hchildone
      have hvalleyiff : Valley child ↔ Valley p ∧ cut = one + 1 := by
        rw [hchildvalley, hvalleyparent]
        exact maximum_insertion_valley_iff n p hparent.1 one cut honecut hb
      change label (n + 1) child = _
      unfold label
      rw [if_neg hnotfirst, hvalleyiff]
      by_cases hh : Valley p ∧ cut = one + 1
      · simp only [if_pos hh]
      · simp only [if_neg hh]
    let active := {cut : ℕ // cut ≤ p.length ∧ p.insertIdx cut (n + 1) ∈
      avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]}
    have hbinary (last : ℕ) (hlastpos : 0 < last) (hlastbound : last ≤ p.length)
        (hshape : ∀ cut, cut ≤ p.length →
          (p.insertIdx cut (n + 1) ∈
            avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔ cut = 0 ∨ cut = last)) :
        ∃ correspondence : Unit ⊕ Unit ≃ active,
          (∀ token, (correspondence (.inl token)).val = 0) ∧
          ∀ token, (correspondence (.inr token)).val = last := by
      let correspondence : Unit ⊕ Unit ≃ active :=
        { toFun := fun edge => match edge with
            | .inl _ => ⟨0, by omega, hfront⟩
            | .inr _ => ⟨last, hlastbound, (hshape last hlastbound).mpr (Or.inr rfl)⟩
          invFun := fun cut => if cut.val = 0 then .inl () else .inr ()
          left_inv := by
            intro edge
            rcases edge with token | token <;> cases token
            · simp
            · simp [show last ≠ 0 by omega]
          right_inv := by
            intro cut
            apply Subtype.ext
            have hc := (hshape cut.val cut.property.1).mp cut.property.2
            rcases hc with hc | hc
            · simp [hc]
            · simp [hc, show last ≠ 0 by omega] }
      exact ⟨correspondence, by intro token; rfl, by intro token; rfl⟩
    have hternary (first last : ℕ) (hfirstpos : 0 < first) (hfirstlast : first < last)
        (hlastbound : last ≤ p.length)
        (hshape : ∀ cut, cut ≤ p.length →
          (p.insertIdx cut (n + 1) ∈
            avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
              cut = 0 ∨ cut = first ∨ cut = last)) :
        ∃ correspondence : (Unit ⊕ Unit) ⊕ Unit ≃ active,
          (∀ token, (correspondence (.inl (.inl token))).val = 0) ∧
          (∀ token, (correspondence (.inl (.inr token))).val = first) ∧
          ∀ token, (correspondence (.inr token)).val = last := by
      let correspondence : (Unit ⊕ Unit) ⊕ Unit ≃ active :=
        { toFun := fun edge => match edge with
            | .inl (.inl _) => ⟨0, by omega, hfront⟩
            | .inl (.inr _) => ⟨first, by omega,
                (hshape first (by omega)).mpr (Or.inr (Or.inl rfl))⟩
            | .inr _ => ⟨last, hlastbound, (hshape last hlastbound).mpr (Or.inr (Or.inr rfl))⟩
          invFun := fun cut => if cut.val = 0 then .inl (.inl ())
            else if cut.val = first then .inl (.inr ()) else .inr ()
          left_inv := by
            intro edge
            rcases edge with (token | token) | token <;> cases token
            · simp
            · simp [show first ≠ 0 by omega]
            · simp [show last ≠ 0 by omega, show last ≠ first by omega]
          right_inv := by
            intro cut
            apply Subtype.ext
            have hc := (hshape cut.val cut.property.1).mp cut.property.2
            rcases hc with hc | hc | hc
            · simp [hc]
            · simp [hc, show first ≠ 0 by omega]
            · simp [hc, show last ≠ 0 by omega, show last ≠ first by omega] }
      exact ⟨correspondence, by intro token; rfl, by intro token; rfl, by intro token; rfl⟩
    rcases hcase with ⟨hfirstmax, hshape⟩ | ⟨first, last, hfirstpos, hfirstlast,
      hlastbound, hfirstmax, hvalleyadj, hdecreasing, hshape⟩
    · by_cases hv : Valley p
      · have hparentlabel : label n p = .T := by
          simp only [label, if_pos hfirstmax, if_pos hv]
        have hdec := hvalleyparent.mp hv
        have hsites : ∀ cut, cut ≤ p.length →
            (p.insertIdx cut (n + 1) ∈
              avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔ cut = 0 ∨ cut = one + 1) := by
          intro cut hb
          rw [hshape cut hb, ← hvalleyparent]
          simp only [hv, and_true]
        obtain ⟨correspondence, hleft, hright⟩ := hbinary (one + 1) (by omega) (by omega) hsites
        rw [hparentlabel]
        dsimp only [Paths]
        refine ⟨correspondence, ?_⟩
        intro edge
        rcases edge with token | token
        · change label (n + 1) (p.insertIdx (correspondence (.inl token)).val (n + 1)) = .T
          rw [hleft token]
          simpa only [hv, if_true, nextLabel] using hfrontlabel
        · change label (n + 1) (p.insertIdx (correspondence (.inr token)).val (n + 1)) = .S
          rw [hright token]
          have ha := (hsites (one + 1) (by omega)).mpr (Or.inr rfl)
          simpa only [hv, true_and, if_true, nextLabel] using
            hpositivelabel (one + 1) (by omega) (by omega) ha
      · have hparentlabel : label n p = .V := by
          simp only [label, if_pos hfirstmax, if_neg hv]
        have hnotdec : ¬ ∀ earlier later, one < earlier → earlier < later →
            later < p.length →
            p.getD later 0 < p.getD earlier 0 := by simpa only [← hvalleyparent] using hv
        have hsites : ∀ cut, cut ≤ p.length →
            (p.insertIdx cut (n + 1) ∈
              avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔ cut = 0) := by
          intro cut hb
          simpa only [hnotdec, and_false, or_false] using hshape cut hb
        let correspondence : Unit ≃ active :=
          { toFun := fun _ => ⟨0, by omega, hfront⟩
            invFun := fun _ => ()
            left_inv := by intro token; cases token; rfl
            right_inv := by intro cut; apply Subtype.ext; exact ((hsites _ cut.property.1).mp
              cut.property.2).symm }
        rw [hparentlabel]
        dsimp only [Paths]
        refine ⟨correspondence, ?_⟩
        intro edge
        change label (n + 1) (p.insertIdx 0 (n + 1)) = nextLabel .V edge
        simpa only [correspondence, hv, if_false, nextLabel] using hfrontlabel
    · have hnotfirst : p.getD 0 0 ≠ n := by
        intro heq
        have hi := (List.getD_inj (by omega) (by omega)
          (hparent.1.nodup_iff.mpr (List.nodup_range' 1))).mp (heq.trans hfirstmax.symm)
        omega
      have hfirstactive := (hshape first (by omega)).mpr (Or.inr (Or.inl rfl))
      have hlastactive := (hshape last hlastbound).mpr (Or.inr (Or.inr rfl))
      have honefirst := hpositiveone first hfirstpos (by omega) hfirstactive
      have hlastnotone : last ≠ one + 1 := by omega
      obtain ⟨correspondence, hzero, hfirst, hlast⟩ :=
        hternary first last hfirstpos hfirstlast hlastbound hshape
      by_cases hv : Valley p
      · have hparentlabel : label n p = .S := by
          simp only [label, if_neg hnotfirst, if_pos hv]
        have hfirstone := hvalleyadj (hvalleyparent.mp hv)
        rw [hparentlabel]
        dsimp only [Paths]
        refine ⟨correspondence, ?_⟩
        intro edge
        rcases edge with (token | token) | token
        · change label (n + 1)
            (p.insertIdx (correspondence (.inl (.inl token))).val (n + 1)) = .T
          rw [hzero token]
          simpa only [hv, if_true, nextLabel] using hfrontlabel
        · change label (n + 1)
            (p.insertIdx (correspondence (.inl (.inr token))).val (n + 1)) = .S
          rw [hfirst token]
          simpa only [hv, hfirstone, true_and, if_true, nextLabel] using
            hpositivelabel first hfirstpos (by omega) hfirstactive
        · change label (n + 1) (p.insertIdx (correspondence (.inr token)).val (n + 1)) = .U
          rw [hlast token]
          simpa only [hv, hlastnotone, and_false, if_false, nextLabel] using
            hpositivelabel last (by omega) hlastbound hlastactive
      · have hparentlabel : label n p = .U := by
          simp only [label, if_neg hnotfirst, if_neg hv]
        rw [hparentlabel]
        dsimp only [Paths]
        refine ⟨correspondence, ?_⟩
        intro edge
        rcases edge with (token | token) | token
        · change label (n + 1)
            (p.insertIdx (correspondence (.inl (.inl token))).val (n + 1)) = .V
          rw [hzero token]
          simpa only [hv, if_false, nextLabel] using hfrontlabel
        · change label (n + 1)
            (p.insertIdx (correspondence (.inl (.inr token))).val (n + 1)) = .U
          rw [hfirst token]
          simpa only [hv, false_and, if_false, nextLabel] using
            hpositivelabel first hfirstpos (by omega) hfirstactive
        · change label (n + 1) (p.insertIdx (correspondence (.inr token)).val (n + 1)) = .U
          rw [hlast token]
          simpa only [hv, false_and, if_false, nextLabel] using
            hpositivelabel last (by omega) hlastbound hlastactive
  
  have hfinite (n : ℕ) : (avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset
    intro p hp
    exact List.mem_permutations.mpr hp.1
  let (n : ℕ) : Fintype (avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]) := (hfinite n).fintype
  let active (n : ℕ) (parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]) :=
    {cut : ℕ // cut ≤ parent.val.length ∧ parent.val.insertIdx cut (n + 1) ∈
      avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]}
  let edgeMap (n : ℕ) (hn : 1 ≤ n) (parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]) :
      Paths 1 (label n parent.val) ≃ active n parent :=
    Classical.choose (C_labelled_edges n parent.val hn parent.property)
  have hedgeLabel (n : ℕ) (hn : 1 ≤ n)
      (parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]])
      (edge : Paths 1 (label n parent.val)) :
      label (n + 1) (parent.val.insertIdx (edgeMap n hn parent edge).val (n + 1)) =
        nextLabel (label n parent.val) edge :=
    Classical.choose_spec (C_labelled_edges n parent.val hn parent.property) edge
  let weighted (n depth : ℕ) := ∑ parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]],
    Nat.card (Paths depth (label n parent.val))
  have hbranches (mark : Label) (depth : ℕ) :
      (∑ edge : Paths 1 mark, Nat.card (Paths depth (nextLabel mark edge))) =
        Nat.card (Paths (depth + 1) mark) := by
    cases mark with
    | T =>
      have transfer : (∑ edge : Unit ⊕ Unit, Nat.card (Paths depth (nextLabel .T edge))) =
          Nat.card (Paths (depth + 1) .T) := by simp [nextLabel, Fintype.sum_sum_type, Paths]
      convert transfer using 1
      apply Finset.sum_congr
      · exact congrArg (fun finiteType : Fintype (Paths 1 .T) => finiteType.elems)
          (Subsingleton.elim _ _)
      · intro edge _; rfl
    | S =>
      have transfer : (∑ edge : (Unit ⊕ Unit) ⊕ Unit, Nat.card (Paths depth (nextLabel .S edge))) =
          Nat.card (Paths (depth + 1) .S) := by simp [nextLabel, Fintype.sum_sum_type, Paths]
      convert transfer using 1
      apply Finset.sum_congr
      · exact congrArg (fun finiteType : Fintype (Paths 1 .S) => finiteType.elems)
          (Subsingleton.elim _ _)
      · intro edge _; rfl
    | U =>
      have transfer : (∑ edge : (Unit ⊕ Unit) ⊕ Unit, Nat.card (Paths depth (nextLabel .U edge))) =
          Nat.card (Paths (depth + 1) .U) := by simp [nextLabel, Fintype.sum_sum_type, Paths]
      convert transfer using 1
      apply Finset.sum_congr
      · exact congrArg (fun finiteType : Fintype (Paths 1 .U) => finiteType.elems)
          (Subsingleton.elim _ _)
      · intro edge _; rfl
    | V =>
      have transfer : (∑ edge : Unit, Nat.card (Paths depth (nextLabel .V edge))) =
          Nat.card (Paths (depth + 1) .V) := by simp [nextLabel, Paths]
      convert transfer using 1
      apply Finset.sum_congr
      · exact congrArg (fun finiteType : Fintype (Paths 1 .V) => finiteType.elems)
          (Subsingleton.elim _ _)
      · intro edge _; rfl
  have hstep (n : ℕ) (hn : 1 ≤ n) (depth : ℕ) :
      weighted (n + 1) depth = weighted n (depth + 1) := by
    let (parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]) : Fintype (active n parent) :=
      Fintype.ofEquiv (Paths 1 (label n parent.val)) (edgeMap n hn parent)
    let insertion : (Σ parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]], active n parent) →
        avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] := fun entry =>
      ⟨entry.1.val.insertIdx entry.2.val (n + 1), entry.2.property.2⟩
    have hbijective : Function.Bijective insertion := by
      constructor
      · intro first second heq
        have hfirstsite := first.2.property.1
        have hsecondsite := second.2.property.1
        have hchild : first.1.val.insertIdx first.2.val (n + 1) =
            second.1.val.insertIdx second.2.val (n + 1) := congrArg Subtype.val heq
        have hfirstlen : (first.1.val.insertIdx first.2.val (n + 1)).length =
            first.1.val.length + 1 :=
          List.length_insertIdx_of_le_length first.2.property.1 _
        have hsecondlen : (second.1.val.insertIdx second.2.val (n + 1)).length =
            second.1.val.length + 1 :=
          List.length_insertIdx_of_le_length second.2.property.1 _
        have hfirstbound : first.2.val <
            (first.1.val.insertIdx first.2.val (n + 1)).length := by omega
        have hsecondbound : second.2.val <
            (first.1.val.insertIdx first.2.val (n + 1)).length := by rw [hchild]; omega
        have hfirstat : (first.1.val.insertIdx first.2.val (n + 1)).getD first.2.val 0 =
            n + 1 := by
          rw [List.getD_eq_getElem _ 0 hfirstbound]
          exact List.getElem_insertIdx_self _
        have hsecondat : (first.1.val.insertIdx first.2.val (n + 1)).getD second.2.val 0 =
            n + 1 := by
          rw [hchild, List.getD_eq_getElem _ 0 (by omega)]
          exact List.getElem_insertIdx_self _
        have hnodup : (first.1.val.insertIdx first.2.val (n + 1)).Nodup :=
          first.2.property.2.1.nodup_iff.mpr (List.nodup_range' 1)
        have hsites : first.2.val = second.2.val :=
          (List.getD_inj hfirstbound hsecondbound hnodup).mp (hfirstat.trans hsecondat.symm)
        have hparents : first.1.val = second.1.val := by
          rw [hsites] at hchild
          exact List.insertIdx_injective _ _ hchild
        rcases first with ⟨parent, cut⟩
        rcases second with ⟨other, othercut⟩
        have hp : parent = other := Subtype.ext hparents
        subst other
        exact congrArg (Sigma.mk parent) (Subtype.ext hsites)
      · intro child
        have hlen : child.val.length = n + 1 := by
          simpa only [List.length_range'] using child.property.1.length_eq
        have hmaxmem : n + 1 ∈ child.val := by
          apply child.property.1.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨n, by omega, by omega⟩
        obtain ⟨site, hsitechild, hvalue⟩ := List.mem_iff_getElem.mp hmaxmem
        let parent := child.val.eraseIdx site
        have hinverse : parent.insertIdx site (n + 1) = child.val := by
          simpa only [parent, hvalue] using List.insertIdx_eraseIdx_getElem hsitechild
        have hparentlen : parent.length = n := by
          simp only [parent, List.length_eraseIdx_of_lt hsitechild, hlen]
          omega
        have hsite : site ≤ parent.length := by omega
        have hparentperm : parent.Perm (List.range' 1 n) := by
          have hcons : ((n + 1) :: parent).Perm child.val := by
            simpa only [parent, hvalue] using List.getElem_cons_eraseIdx_perm hsitechild
          have hrange : (List.range' 1 (n + 1)).Perm ((n + 1) :: List.range' 1 n) := by
            rw [List.range'_concat]
            simpa [Nat.add_comm] using
              (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
          exact (hcons.trans (child.property.1.trans hrange)).cons_inv
        have hmaxparent : ∀ value ∈ parent, value < n + 1 := by
          intro value hvalue
          have hm := hparentperm.mem_iff.mp hvalue
          simp only [List.mem_range', Nat.one_mul] at hm
          obtain ⟨offset, hoffset, heq⟩ := hm
          omega
        have hparentmember : parent ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]] := by
          refine ⟨hparentperm, ?_, ?_⟩
          · apply (isFishburn_insertIdx_max_iff parent (n + 1) site hsite hmaxparent).mp
              (by rw [hinverse]; exact child.property.2.1) |>.1
          · intro pattern hpattern hocc
            obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
            apply child.property.2.2 pattern hpattern
            refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist child.val site),
              by simp⟩
            intro rank hlow hhigh
            exact (List.eraseIdx_sublist child.val site).subset (hmem rank hlow hhigh)
        refine ⟨⟨⟨parent, hparentmember⟩, ⟨site, hsite, ?_⟩⟩, ?_⟩
        · rw [hinverse]
          exact child.property
        · exact Subtype.ext hinverse
    let correspondence := Equiv.ofBijective insertion hbijective
    calc
      weighted (n + 1) depth =
          ∑ entry : (Σ parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]], active n parent),
            Nat.card (Paths depth (label (n + 1) (insertion entry).val)) :=
        (correspondence.sum_comp (fun child =>
          Nat.card (Paths depth (label (n + 1) child.val)))).symm
      _ = ∑ parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]],
          ∑ cut : active n parent,
            Nat.card (Paths depth (label (n + 1) (parent.val.insertIdx cut.val (n + 1)))) := by
        rw [Fintype.sum_sigma]
      _ = weighted n (depth + 1) := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [← (edgeMap n hn parent).sum_comp (fun cut =>
          Nat.card (Paths depth (label (n + 1) (parent.val.insertIdx cut.val (n + 1)))))]
        calc
          _ = ∑ edge : Paths 1 (label n parent.val),
                Nat.card (Paths depth (nextLabel (label n parent.val) edge)) := by
            apply Finset.sum_congr rfl
            intro edge _
            rw [hedgeLabel n hn parent edge]
          _ = _ := hbranches (label n parent.val) depth
  have hroot : [1] ∈ avoiders 1 [[1, 4, 2, 3], [3, 1, 2, 4]] := by
    refine ⟨by decide, ?_, ?_⟩
    · intro before later hgap hlater
      change later < 1 at hlater
      omega
    · intro pattern hm hocc
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := by simpa using hm
      rcases hc with rfl | rfl <;>
        obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
        have hb := hsub.length_le <;> simp only [List.length_map] at hb <;> change 4 ≤ 1 at hb
      all_goals omega
  let root : avoiders 1 [[1, 4, 2, 3], [3, 1, 2, 4]] := ⟨[1], hroot⟩
  have hrootlabel : label 1 root.val = .T := by
    have hv : Valley [1] := by
      refine ⟨0, by decide, rfl, ?_⟩
      intro earlier later he hl hb
      change later < 1 at hb
      omega
    simp only [root, label, show ([1] : List ℕ).getD 0 0 = 1 by rfl, if_true, hv]
  have hrootweight (depth : ℕ) : weighted 1 depth = Nat.card (Paths depth .T) := by
    have hall (parent : avoiders 1 [[1, 4, 2, 3], [3, 1, 2, 4]]) : parent = root := by
      apply Subtype.ext
      have hp : parent.val.Perm [1] := parent.property.1
      exact List.perm_singleton.mp hp
    calc
      weighted 1 depth = Nat.card (Paths depth (label 1 root.val)) := by
        apply Finset.sum_eq_single root
        · intro other _ hne
          exact False.elim (hne (hall other))
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ root))
      _ = _ := by rw [hrootlabel]
  have htransfer : ∀ n : ℕ, 1 ≤ n → ∀ depth,
      weighted n depth = Nat.card (Paths (depth + n - 1) .T) := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro hn depth
      by_cases hz : n = 0
      · subst n
        simpa using hrootweight depth
      · rw [hstep n (by omega) depth, ih (by omega) (depth + 1)]
        congr 2
        omega
  have hweightzero (n : ℕ) : weighted n 0 =
      Nat.card (avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]) := by
    have hunit (mark : Label) : Nat.card (Paths 0 mark) = 1 := by
      change Nat.card Unit = 1
      simp
    change (∑ parent : avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]],
      Nat.card (Paths 0 (label n parent.val))) = _
    simp only [hunit, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Nat.card_eq_fintype_card, Nat.cast_id]
  have hcard : Nat.card (avoiders size [[1, 4, 2, 3], [3, 1, 2, 4]]) =
      (size - 1) * 2 ^ (size - 2) + 1 := by
    rw [← hweightzero size, htransfer size hsize 0, hpathcount]
    simp only [Nat.zero_add, Nat.sub_sub, Nat.reduceAdd]
  simpa only [Nat.card_coe_set_eq] using hcard

end D5.S3.Combinatorics.Fishburn.FishburnTenFourCLabels
