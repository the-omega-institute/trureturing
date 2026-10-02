/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentPermChildren
   mirror-E: none(waiver:permutation-child-correspondence)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Maximum-insertion children are bijectively indexed by the common labelled rule. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentSites
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentPermChildren

open WeakAscentDefs WeakAscentChildren WeakAscentInsertion WeakAscentSites

noncomputable def permLabel (p : List ℕ) : ℕ × ℕ :=
  (((activeSites p).filter (p.idxOf p.length < ·)).card, (recordSites p).card)

theorem permutation_children_rule (p : List ℕ) (hempty : p ≠ [])
    (hperm : p.Perm (List.range' 1 p.length)) (havoid : ¬ ContainsV2413 p) :
    0 < (permLabel p).1 ∧ 0 < (permLabel p).2 ∧
    ∃ correspondence :
      {q : List ℕ // ∃ site, site ∈ activeSites p ∧
        q = p.insertIdx site (p.length + 1)} ≃
        (Fin (permLabel p).1 ⊕ Fin (permLabel p).2),
      ∀ q, permLabel q.val =
        childLabel (permLabel p).1 (permLabel p).2 (correspondence q) := by
  classical
  let maximum := p.length + 1
  let position := p.idxOf p.length
  let rightSites := (activeSites p).filter (position < ·)
  let leftSites := recordSites p
  have hstructure := active_record_structure p hempty hperm havoid
  change (activeSites p).filter (· ≤ position) = leftSites ∧
    (∀ site ∈ leftSites, site ≤ position) ∧ 0 ∈ activeSites p ∧
    p.length ∈ activeSites p at hstructure
  have hmaxpos : position < p.length := by
    apply List.idxOf_lt_length_iff.mpr
    apply hperm.mem_iff.mpr
    exact List.mem_range'.mpr ⟨p.length - 1,
      by have := List.length_pos_iff.mpr hempty; omega,
      by have := List.length_pos_iff.mpr hempty; omega⟩
  have active_bound (site : ℕ) (hsite : site ∈ activeSites p) : site ≤ p.length := by
    have hbound := (Finset.mem_filter.mp hsite).1
    have := Finset.mem_range.mp hbound
    omega
  have pbound (value : ℕ) (hvalue : value ∈ p) : value < maximum := by
    obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hvalue)
    dsimp [maximum]
    omega
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range')
  have left_active (site : ℕ) (hsite : site ∈ leftSites) : site ∈ activeSites p := by
    have hmem : site ∈ (activeSites p).filter (· ≤ position) := by
      rw [hstructure.1]
      exact hsite
    exact (Finset.mem_filter.mp hmem).1
  have hrightpos : 0 < rightSites.card := by
    apply Finset.card_pos.mpr
    exact ⟨p.length, Finset.mem_filter.mpr ⟨hstructure.2.2.2, hmaxpos⟩⟩
  have hleftpos : 0 < leftSites.card := by
    apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    rw [← hstructure.1]
    exact Finset.mem_filter.mpr ⟨hstructure.2.2.1, Nat.zero_le _⟩
  let partition : activeSites p ≃ (rightSites ⊕ leftSites) :=
    { toFun := fun site => if hright : position < site.val then
        .inl ⟨site.val, Finset.mem_filter.mpr ⟨site.property, hright⟩⟩
      else .inr ⟨site.val, by
        rw [← hstructure.1]
        exact Finset.mem_filter.mpr ⟨site.property, by omega⟩⟩
      invFun := fun side => match side with
        | .inl site => ⟨site.val, (Finset.mem_filter.mp site.property).1⟩
        | .inr site => ⟨site.val, left_active site.val site.property⟩
      left_inv := by
        intro site
        dsimp only
        split_ifs <;> rfl
      right_inv := by
        intro side
        cases side with
        | inl site =>
          dsimp only
          rw [dif_pos (Finset.mem_filter.mp site.property).2]
        | inr site =>
          dsimp only
          have hleft := hstructure.2.1 site.val site.property
          rw [dif_neg (by omega)] }
  let ranks : rightSites ⊕ leftSites ≃ (Fin rightSites.card ⊕ Fin leftSites.card) :=
    Equiv.sumCongr ((rightSites.orderIsoOfFin rfl).toEquiv.symm.trans Fin.revPerm)
      (leftSites.orderIsoOfFin rfl).toEquiv.symm
  have maximum_position (site : activeSites p) :
      (p.insertIdx site.val maximum).idxOf maximum = site.val := by
    let q := p.insertIdx site.val maximum
    have hsite := active_bound site.val site.property
    have hlength : q.length = p.length + 1 := by simp [q, List.length_insertIdx, hsite]
    have hqnodup : q.Nodup := (List.perm_insertIdx maximum p hsite).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨by intro hmem; have := pbound maximum hmem; omega, hnodup⟩)
    have hmem : maximum ∈ q := (List.mem_insertIdx hsite).mpr (Or.inl rfl)
    have hindex : q.idxOf maximum < q.length := List.idxOf_lt_length_iff.mpr hmem
    have hread : q.getD (q.idxOf maximum) 0 = maximum := by
      rw [List.getD_eq_getElem _ _ hindex, List.getElem_idxOf hindex]
    have hsite_read : q.getD site.val 0 = maximum := by
      simp [q, List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hsite]
    exact (List.getD_inj hindex (by omega) hqnodup).mp (hread.trans hsite_read.symm)
  let insertChild : activeSites p →
      {q : List ℕ // ∃ site, site ∈ activeSites p ∧ q = p.insertIdx site maximum} :=
    fun site => ⟨p.insertIdx site.val maximum, site.val, site.property, rfl⟩
  have insert_bijective : Function.Bijective insertChild := by
    constructor
    · intro first second heq
      have hsame := congrArg (fun q => q.val.idxOf maximum) heq
      change (p.insertIdx first.val maximum).idxOf maximum =
        (p.insertIdx second.val maximum).idxOf maximum at hsame
      rw [maximum_position first, maximum_position second] at hsame
      exact Subtype.ext hsame
    · intro child
      obtain ⟨site, hsite, heq⟩ := child.property
      exact ⟨⟨site, hsite⟩, Subtype.ext heq.symm⟩
  let insertEquiv := Equiv.ofBijective insertChild insert_bijective
  let correspondence := insertEquiv.symm.trans (partition.trans ranks)
  have initial_rank (sites : Finset ℕ) (site : sites) :
      (sites.filter (· < site.val)).card =
        ((sites.orderIsoOfFin rfl).symm site).val := by
    let iso := sites.orderIsoOfFin rfl
    let rank := iso.symm site
    have mapped : (sites.filter (· < site.val)).card = (Finset.range rank.val).card := by
      apply Finset.card_bij (fun value hvalue => (iso.symm
        ⟨value, (Finset.mem_filter.mp hvalue).1⟩).val)
      · intro value hvalue
        apply Finset.mem_range.mpr
        have hlt : (⟨value, (Finset.mem_filter.mp hvalue).1⟩ : sites) < site :=
          (Finset.mem_filter.mp hvalue).2
        exact iso.symm.strictMono hlt
      · intro first hfirst second hsecond heq
        have hsame : iso.symm ⟨first, (Finset.mem_filter.mp hfirst).1⟩ =
            iso.symm ⟨second, (Finset.mem_filter.mp hsecond).1⟩ := Fin.ext heq
        exact congrArg Subtype.val (iso.symm.injective hsame)
      · intro index hindex
        have hlt := Finset.mem_range.mp hindex
        let ordinal : Fin sites.card := ⟨index, by have := rank.isLt; omega⟩
        have hbefore : ordinal < rank := hlt
        have hvalue : iso ordinal < site := by
          have hlt' := iso.strictMono hbefore
          change iso ordinal < iso (iso.symm site) at hlt'
          rwa [OrderIso.apply_symm_apply] at hlt'
        refine ⟨(iso ordinal).val,
          Finset.mem_filter.mpr ⟨(iso ordinal).property, hvalue⟩, ?_⟩
        change (iso.symm (iso ordinal)).val = index
        rw [OrderIso.symm_apply_apply]
    simpa only [Finset.card_range] using mapped
  have split_card (sites : Finset ℕ) (site : sites) :
      (sites.filter (· < site.val)).card + 1 + (sites.filter (site.val < ·)).card =
        sites.card := by
    have hbefore : sites.filter (· ≤ site.val) =
        insert site.val (sites.filter (· < site.val)) := by
      ext value
      simp only [Finset.mem_filter, Finset.mem_insert]
      by_cases heq : value = site.val
      · subst value
        simp [site.property]
      · simp only [heq, false_or]
        constructor <;> rintro ⟨hmem, hbound⟩ <;> exact ⟨hmem, by omega⟩
    have hnotmem : site.val ∉ sites.filter (· < site.val) := by simp
    have hsplit := Finset.card_filter_add_card_filter_not (s := sites) (· ≤ site.val)
    have hafter : sites.filter (fun value => ¬ value ≤ site.val) =
        sites.filter (site.val < ·) := by
      ext value
      simp only [Finset.mem_filter, not_le]
    rw [hbefore, Finset.card_insert_of_notMem hnotmem, hafter] at hsplit
    exact hsplit
  have child_counts (site : activeSites p) :
      permLabel (p.insertIdx site.val maximum) =
        (1 + ((activeSites p).filter (site.val < ·)).card,
          1 + (leftSites.filter (· < site.val)).card) := by
    let q := p.insertIdx site.val maximum
    have hsite := active_bound site.val site.property
    have hlength : q.length = p.length + 1 := by simp [q, List.length_insertIdx, hsite]
    have hposition : q.idxOf q.length = site.val := by
      rw [hlength]
      exact maximum_position site
    have old_read (index : ℕ) (hindex : index < site.val) :
        q.getD index 0 = p.getD index 0 := by
      simp [q, List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hindex]
    have maximum_read : q.getD site.val 0 = maximum := by
      simp [q, List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hsite]
    have qbound (index : ℕ) (hindex : index < q.length) : q.getD index 0 ≤ maximum := by
      rw [List.getD_eq_getElem _ _ hindex]
      have hmem := List.getElem_mem hindex
      change q[index] ∈ p.insertIdx site.val maximum at hmem
      rcases (List.mem_insertIdx hsite).mp hmem with heq | hold
      · omega
      · exact Nat.le_of_lt (pbound _ hold)
    have new_records : recordSites q = insert site.val (leftSites.filter (· < site.val)) := by
      ext index
      simp only [recordSites, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨hindex, hrecord⟩
        by_cases heq : index = site.val
        · exact Or.inl heq
        · have hbefore : index < site.val := by
            by_contra hnot
            have hvalue := hrecord site.val (by omega)
            rw [maximum_read] at hvalue
            have hbound := qbound index hindex
            omega
          right
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, hbefore⟩
          intro earlier hearlier
          have hvalue := hrecord earlier hearlier
          rwa [old_read earlier (by omega), old_read index hbefore] at hvalue
      · rintro (heq | ⟨hrecord, hbefore⟩)
        · subst index
          refine ⟨by omega, ?_⟩
          intro earlier hearlier
          rw [old_read earlier hearlier, maximum_read, List.getD_eq_getElem _ _ (by omega)]
          exact pbound _ (List.getElem_mem (show earlier < p.length by omega))
        · refine ⟨by omega, ?_⟩
          intro earlier hearlier
          rw [old_read earlier (by omega), old_read index hbefore]
          exact (Finset.mem_filter.mp hrecord).2 earlier hearlier
    have new_right : (activeSites q).filter (site.val < ·) =
        insert (site.val + 1) (((activeSites p).filter (site.val < ·)).image (· + 1)) := by
      have htransform := active_sites_insert p site.val hperm havoid site.property
      change activeSites q = _ at htransform
      rw [htransform]
      ext index
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_image]
      constructor
      · rintro ⟨((⟨hrecord, hbefore⟩ | (heq | heq)) |
          ⟨old, ⟨hold, hafter⟩, heq⟩), hright⟩
        · omega
        · omega
        · exact Or.inl heq
        · exact Or.inr ⟨old, ⟨hold, hafter⟩, heq⟩
      · rintro (heq | ⟨old, ⟨hold, hafter⟩, heq⟩)
        · exact ⟨Or.inl (Or.inr (Or.inr heq)), by omega⟩
        · exact ⟨Or.inr ⟨old, ⟨hold, hafter⟩, heq⟩, by omega⟩
    have hnorecord : site.val ∉ leftSites.filter (· < site.val) := by simp
    have hnoright : site.val + 1 ∉
        ((activeSites p).filter (site.val < ·)).image (· + 1) := by
      rintro hmem
      obtain ⟨old, hold, heq⟩ := Finset.mem_image.mp hmem
      have hafter := (Finset.mem_filter.mp hold).2
      omega
    rw [permLabel, hposition, new_right, new_records,
      Finset.card_insert_of_notMem hnoright, Finset.card_insert_of_notMem hnorecord,
      Finset.card_image_of_injective _ (fun first second heq => by omega)]
    apply Prod.ext <;> omega
  refine ⟨hrightpos, hleftpos, correspondence, ?_⟩
  intro child
  let site := insertEquiv.symm child
  have hchild : child.val = p.insertIdx site.val maximum := by
    exact (congrArg Subtype.val (insertEquiv.apply_symm_apply child)).symm
  rw [hchild, child_counts]
  change (1 + ((activeSites p).filter (site.val < ·)).card,
      1 + (leftSites.filter (· < site.val)).card) =
    childLabel rightSites.card leftSites.card (ranks (partition site))
  simp only [partition, Equiv.coe_fn_mk]
  split_ifs with hright
  · let right : rightSites := ⟨site.val, Finset.mem_filter.mpr ⟨site.property, hright⟩⟩
    have hrecords : leftSites.filter (· < site.val) = leftSites := by
      apply Finset.filter_eq_self.mpr
      intro record hrecord
      have := hstructure.2.1 record hrecord
      omega
    have hafter : (activeSites p).filter (site.val < ·) = rightSites.filter (site.val < ·) := by
      ext value
      simp only [rightSites, Finset.mem_filter]
      constructor
      · rintro ⟨hmem, hafter⟩
        exact ⟨⟨hmem, by omega⟩, hafter⟩
      · rintro ⟨⟨hmem, _⟩, hafter⟩
        exact ⟨hmem, hafter⟩
    have hsplit := split_card rightSites right
    have hrank := initial_rank rightSites right
    change (rightSites.filter (· < site.val)).card + 1 +
      (rightSites.filter (site.val < ·)).card = rightSites.card at hsplit
    change (rightSites.filter (· < site.val)).card =
      ((rightSites.orderIsoOfFin rfl).symm right).val at hrank
    rw [hrecords, hafter]
    change (1 + (rightSites.filter (site.val < ·)).card, 1 + leftSites.card) =
      ((((rightSites.orderIsoOfFin rfl).symm right).rev).val + 1, leftSites.card + 1)
    rw [Fin.val_rev]
    apply Prod.ext
    · have hindex := ((rightSites.orderIsoOfFin rfl).symm right).isLt
      omega
    · omega
  · have hleft : site.val ∈ leftSites := by
      rw [← hstructure.1]
      exact Finset.mem_filter.mpr ⟨site.property, by omega⟩
    let left : leftSites := ⟨site.val, hleft⟩
    have hbefore : (activeSites p).filter (· < site.val) = leftSites.filter (· < site.val) := by
      ext value
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hvalue, hbefore⟩
        refine ⟨?_, hbefore⟩
        rw [← hstructure.1]
        exact Finset.mem_filter.mpr ⟨hvalue, by omega⟩
      · rintro ⟨hvalue, hbefore⟩
        exact ⟨left_active value hvalue, hbefore⟩
    have htotal : (activeSites p).card = rightSites.card + leftSites.card := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := activeSites p) (position < ·)
      have hnot : (activeSites p).filter (fun value => ¬ position < value) = leftSites := by
        simpa only [not_lt] using hstructure.1
      rw [hnot] at hsplit
      exact hsplit.symm
    have hsplit := split_card (activeSites p) site
    have hrank := initial_rank leftSites left
    change (leftSites.filter (· < site.val)).card =
      ((leftSites.orderIsoOfFin rfl).symm left).val at hrank
    rw [hbefore, htotal] at hsplit
    change (1 + ((activeSites p).filter (site.val < ·)).card,
        1 + (leftSites.filter (· < site.val)).card) =
      (rightSites.card + leftSites.card - ((leftSites.orderIsoOfFin rfl).symm left).val,
        ((leftSites.orderIsoOfFin rfl).symm left).val + 1)
    apply Prod.ext <;> omega

end D5.S3.Combinatorics.WeakAscent.WeakAscentPermChildren
