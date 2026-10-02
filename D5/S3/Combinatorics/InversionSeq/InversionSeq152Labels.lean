/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Labels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Labels
   mirror-E: none(waiver:rank-slack-suffix-bijection)
   anchors: []
   utility: none
   digest: Rank subtraction bijects bounded rotation blocks with ordered label partitions. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Labels

theorem sorted_label_bijection (size lower upper : ℕ) :
    Nonempty
      ({blocks : List (List ℕ) // blocks.flatten.length = size ∧
        (∀ block ∈ blocks, block ≠ []) ∧ blocks.flatten.Pairwise (· < ·) ∧
        (∀ value ∈ blocks.flatten, lower < value) ∧
        ∀ index < (blocks.flatMap (fun block => block.rotate 1)).length,
          (blocks.flatMap (fun block => block.rotate 1)).getD index 0 ≤ upper + 1 + index} ≃
      {blocks : List (List ℕ) // blocks.flatten.length = size ∧
        blocks.flatten.Pairwise (· ≤ ·) ∧
        (∀ label ∈ blocks.flatten, lower ≤ label ∧ label ≤ upper) ∧
        (∀ block ∈ blocks, block ≠ []) ∧
        ∀ block ∈ blocks, ∀ label ∈ block.tail, label < upper}) := by
  have hrank : ∀ values : List ℕ, values.Pairwise (· < ·) →
      ∀ floor : ℕ, (∀ value ∈ values, floor < value) →
      ∀ index < values.length, floor + index + 1 ≤ values.getD index 0 := by
    intro values
    induction values with
    | nil => simp
    | cons first rest ih =>
      intro hsorted floor hfloor index hindex
      have hfirst := hfloor first (by simp)
      obtain ⟨hafter, htail⟩ := List.pairwise_cons.mp hsorted
      cases index with
      | zero => simp only [List.getD_cons_zero]; omega
      | succ index =>
        have hvalue := ih htail first hafter index (by simpa using hindex)
        simp only [List.getD_cons_succ]
        omega
  have hlist (size lower upper : ℕ) :
      ∃ equivalence :
        {values : List ℕ // values.length = size ∧ values.Pairwise (· < ·) ∧
          (∀ value ∈ values, lower < value) ∧
          (∀ index < values.length, values.getD index 0 ≤ upper + index)} ≃
        {labels : List ℕ // labels.length = size ∧ labels.Pairwise (· ≤ ·) ∧
          (∀ label ∈ labels, lower ≤ label ∧ label < upper)},
        (∀ values, (equivalence values).val =
          values.val.mapIdx (fun index value => value - (index + 1))) ∧
        (∀ labels, (equivalence.symm labels).val =
          labels.val.mapIdx (fun index label => label + index + 1)) := by
    have hspacing : ∀ values : List ℕ, values.Pairwise (· < ·) →
        ∀ first second, first < second → second < values.length →
        values.getD first 0 + (second - first) ≤ values.getD second 0 := by
      intro values
      induction values with
      | nil => simp
      | cons entry rest ih =>
        intro hsorted first second hlt hsecond
        obtain ⟨hafter, htail⟩ := List.pairwise_cons.mp hsorted
        cases first with
        | zero =>
          cases second with
          | zero => omega
          | succ second =>
            simpa only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero,
              Nat.add_assoc] using hrank rest htail entry hafter second
                (by simpa using hsecond)
        | succ first =>
          cases second with
          | zero => omega
          | succ second =>
            simpa using ih htail first second (by omega) (by simpa using hsecond)
    have hget (word : List ℕ) (transform : ℕ → ℕ → ℕ) (index : ℕ)
        (hindex : index < word.length) :
        (word.mapIdx transform).getD index 0 = transform index (word.getD index 0) := by
      rw [List.getD_eq_getElem (word.mapIdx transform) 0 (by simpa using hindex),
        List.getElem_mapIdx, List.getD_eq_getElem word 0 hindex]
    refine ⟨{
      toFun := fun values => ?_
      invFun := fun labels => ?_
      left_inv := ?_
      right_inv := ?_ }, ?_, ?_⟩
    · refine ⟨values.val.mapIdx (fun index value => value - (index + 1)), ?_⟩
      refine ⟨by simpa using values.property.1, ?_, ?_⟩
      · apply List.pairwise_iff_getElem.mpr
        intro first second hfirst hsecond hlt
        have hfirstBound := hrank values.val values.property.2.1 lower
          values.property.2.2.1 first (by simpa using hfirst)
        have hsecondBound := hrank values.val values.property.2.1 lower
          values.property.2.2.1 second (by simpa using hsecond)
        have hgap := hspacing values.val values.property.2.1 first second hlt
          (by simpa using hsecond)
        simp only [List.getElem_mapIdx]
        rw [List.getD_eq_getElem _ _ (by simpa using hfirst)] at hfirstBound hgap
        rw [List.getD_eq_getElem _ _ (by simpa using hsecond)] at hsecondBound hgap
        omega
      · intro label hlabel
        obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hlabel
        have hlow := hrank values.val values.property.2.1 lower values.property.2.2.1
          index (by simpa using hindex)
        have hhigh := values.property.2.2.2 index (by simpa using hindex)
        simp only [List.getElem_mapIdx]
        rw [List.getD_eq_getElem _ _ (by simpa using hindex)] at hlow hhigh
        omega
    · refine ⟨labels.val.mapIdx (fun index label => label + index + 1), ?_⟩
      refine ⟨by simpa using labels.property.1, ?_, ?_, ?_⟩
      · apply List.pairwise_iff_getElem.mpr
        intro first second hfirst hsecond hlt
        have hle := List.pairwise_iff_getElem.mp labels.property.2.1 first second
          (by simpa using hfirst) (by simpa using hsecond) hlt
        simp only [List.getElem_mapIdx]
        omega
      · intro value hvalue
        obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hvalue
        have hlow := (labels.property.2.2 _ (List.getElem_mem (by simpa using hindex))).1
        simp only [List.getElem_mapIdx]
        omega
      · intro index hindex
        have hhigh := (labels.property.2.2 _ (List.getElem_mem (by simpa using hindex))).2
        rw [hget labels.val _ index (by simpa using hindex),
          List.getD_eq_getElem _ _ (by simpa using hindex)]
        omega
    · intro values
      apply Subtype.ext
      apply List.ext_getElem
      · simp
      · intro index hleft hright
        have hlow := hrank values.val values.property.2.1 lower values.property.2.2.1
          index hright
        simp only [List.getElem_mapIdx]
        rw [List.getD_eq_getElem _ _ hright] at hlow
        omega
    · intro labels
      apply Subtype.ext
      apply List.ext_getElem
      · simp
      · intro index hleft hright
        simp only [List.getElem_mapIdx]
        omega
    · intro values
      rfl
    · intro labels
      rfl
  classical
  let ranked (transform : ℕ → ℕ → ℕ) (offset : ℕ) (blocks : List (List ℕ)) :=
    blocks.mapIdx fun blockIndex block => block.mapIdx fun index value =>
      transform (offset + (blocks.take blockIndex).flatten.length + index) value
  have hnil (transform : ℕ → ℕ → ℕ) (offset : ℕ) :
      ranked transform offset [] = [] := rfl
  have hcons (transform : ℕ → ℕ → ℕ) (offset : ℕ) (block : List ℕ)
      (rest : List (List ℕ)) :
      ranked transform offset (block :: rest) =
        block.mapIdx (fun index value => transform (offset + index) value) ::
          ranked transform (offset + block.length) rest := by
    simp [ranked, List.mapIdx_cons, Nat.add_assoc]
  have hflat (transform : ℕ → ℕ → ℕ) (offset : ℕ) (blocks : List (List ℕ)) :
      (ranked transform offset blocks).flatten =
        blocks.flatten.mapIdx (fun index value => transform (offset + index) value) := by
    induction blocks generalizing offset with
    | nil => simp [hnil]
    | cons block rest ih =>
      simp only [hcons, List.flatten_cons, ih, List.mapIdx_append]
      congr 2
      funext index value
      congr 1
      omega
  have hshape (transform : ℕ → ℕ → ℕ) (offset : ℕ) (blocks : List (List ℕ)) :
      (ranked transform offset blocks).map List.length = blocks.map List.length := by
    induction blocks generalizing offset with
    | nil => rfl
    | cons block rest ih => simp only [hcons, List.map_cons, List.length_mapIdx, ih]
  have hnonempty (transform : ℕ → ℕ → ℕ) (offset : ℕ) (blocks : List (List ℕ))
      (hne : ∀ block ∈ blocks, block ≠ []) :
      ∀ block ∈ ranked transform offset blocks, block ≠ [] := by
    induction blocks generalizing offset with
    | nil => simp [hnil]
    | cons block rest ih =>
      simp only [hcons, List.mem_cons]
      intro image himage
      rcases himage with rfl | himage
      · exact List.mapIdx_ne_nil_iff.mpr (hne block (by simp))
      · exact ih _ (fun item hitem => hne item (by simp [hitem])) image himage
  have hprefix (transform : ℕ → ℕ → ℕ) (offset : ℕ) (blocks : List (List ℕ))
      (index : ℕ) :
      ((ranked transform offset blocks).take index).flatten.length =
        (blocks.take index).flatten.length := by
    induction blocks generalizing offset index with
    | nil => simp [hnil]
    | cons block rest ih =>
      cases index with
      | zero => simp
      | succ index =>
        simp only [hcons, List.take_succ_cons, List.flatten_cons, List.length_append,
          List.length_mapIdx, ih]
  have hblock (transform : ℕ → ℕ → ℕ) (offset : ℕ) (blocks : List (List ℕ))
      (index : ℕ) :
      (ranked transform offset blocks).getD index [] =
        (blocks.getD index []).mapIdx (fun position value =>
          transform (offset + (blocks.take index).flatten.length + position) value) := by
    induction blocks generalizing offset index with
    | nil => simp [hnil]
    | cons block rest ih =>
      cases index with
      | zero => simp [hcons]
      | succ index =>
        simp only [hcons, List.getD_cons_succ, List.take_succ_cons, List.flatten_cons,
          List.length_append, ih, Nat.add_assoc]
  have htail (word : List ℕ) (transform : ℕ → ℕ → ℕ) (index : ℕ)
      (hindex : index < word.tail.length) :
      (word.mapIdx transform).tail.getD index 0 =
        transform (index + 1) (word.tail.getD index 0) := by
    cases word with
    | nil => simp at hindex
    | cons first rest =>
      simp only [List.mapIdx_cons, List.tail_cons]
      rw [List.getD_eq_getElem _ _ (by simpa using hindex), List.getElem_mapIdx,
        List.getD_eq_getElem rest 0 (by simpa using hindex)]
      rfl
  have hext : ∀ first second : List (List ℕ),
      first.map List.length = second.map List.length →
      first.flatten = second.flatten → first = second := by
    intro first
    induction first with
    | nil => intro second hlen _; simpa using hlen.symm
    | cons block rest ih =>
      intro second hlen hflat
      cases second with
      | nil => simp at hlen
      | cons other more =>
        obtain ⟨hlen, hlens⟩ := List.cons.inj hlen
        have hfirst := congrArg (List.take block.length) hflat
        simp only [List.flatten_cons, List.take_left] at hfirst
        rw [hlen, List.take_left] at hfirst
        subst other
        have hrest := List.append_cancel_left hflat
        exact congrArg (List.cons block) (ih more hlens hrest)
  let Source := {blocks : List (List ℕ) // blocks.flatten.length = size ∧
    (∀ block ∈ blocks, block ≠ []) ∧ blocks.flatten.Pairwise (· < ·) ∧
    (∀ value ∈ blocks.flatten, lower < value) ∧
    ∀ index < (blocks.flatMap (fun block => block.rotate 1)).length,
      (blocks.flatMap (fun block => block.rotate 1)).getD index 0 ≤ upper + 1 + index}
  let Target := {blocks : List (List ℕ) // blocks.flatten.length = size ∧
    blocks.flatten.Pairwise (· ≤ ·) ∧
    (∀ label ∈ blocks.flatten, lower ≤ label ∧ label ≤ upper) ∧
    (∀ block ∈ blocks, block ≠ []) ∧
    ∀ block ∈ blocks, ∀ label ∈ block.tail, label < upper}
  obtain ⟨equivalence, hdown, hup⟩ := hlist size lower (upper + 1)
  let down := ranked (fun index value => value - (index + 1)) 0
  let up := ranked (fun index label => label + index + 1) 0
  have hdownValid (blocks : Source) :
      (down blocks.1).flatten.length = size ∧
      (down blocks.1).flatten.Pairwise (· ≤ ·) ∧
      (∀ label ∈ (down blocks.1).flatten, lower ≤ label ∧ label ≤ upper) ∧
      (∀ block ∈ down blocks.1, block ≠ []) ∧
      ∀ block ∈ down blocks.1, ∀ label ∈ block.tail, label < upper := by
    obtain ⟨hsortedBound, hjoined⟩ :=
      (InversionSeq152Bounds.rotated_suffix_bounds_iff blocks.1 (upper + 1)
        blocks.2.2.1 blocks.2.2.2.1).mp blocks.2.2.2.2.2
    let values : {values : List ℕ // values.length = size ∧ values.Pairwise (· < ·) ∧
        (∀ value ∈ values, lower < value) ∧
        ∀ index < values.length, values.getD index 0 ≤ upper + 1 + index} :=
      ⟨blocks.1.flatten, blocks.2.1, blocks.2.2.2.1,
      blocks.2.2.2.2.1, hsortedBound⟩
    have hvalues : (down blocks.1).flatten = (equivalence values).1 := by
      rw [hdown]; simpa [down] using hflat (fun index value => value - (index + 1)) 0 _
    refine ⟨?_, ?_, ?_, hnonempty (fun index value => value - (index + 1)) 0 _
      blocks.2.2.1, ?_⟩
    · rw [hvalues]; exact (equivalence values).2.1
    · rw [hvalues]; exact (equivalence values).2.2.1
    · rw [hvalues]
      intro label hlabel
      have := (equivalence values).2.2.2 label hlabel
      omega
    · intro block hmem label hlabel
      obtain ⟨blockIndex, hbIndex, hblockEq⟩ := List.mem_iff_getElem.mp hmem
      have hbLength : (down blocks.1).length = blocks.1.length := by
        simpa only [List.length_map] using congrArg List.length
          (hshape (fun index value => value - (index + 1)) 0 blocks.1)
      have hbIndex' : blockIndex < blocks.1.length := by omega
      have hb := hblock (fun index value => value - (index + 1)) 0 blocks.1 blockIndex
      change (down blocks.1).getD blockIndex [] = _ at hb
      rw [List.getD_eq_getElem _ _ hbIndex, hblockEq] at hb
      obtain ⟨index, hi, hlabelEq⟩ := List.mem_iff_getElem.mp hlabel
      have hi' : index < (blocks.1.getD blockIndex []).tail.length := by
        rw [hb] at hi
        simpa only [List.length_tail, List.length_mapIdx] using hi
      have hv := hjoined blockIndex hbIndex' index hi'
      have hdecomp : blocks.1.flatten = (blocks.1.take blockIndex).flatten ++
          (blocks.1.getD blockIndex []) ++ (blocks.1.drop (blockIndex + 1)).flatten := by
        have hsplit := congrArg List.flatten
          (List.take_append_drop (blockIndex + 1) blocks.1)
        rw [List.take_succ_eq_append_getElem hbIndex', List.flatten_append,
          List.flatten_append, List.flatten_singleton] at hsplit
        simpa only [List.getD_eq_getElem _ _ hbIndex'] using hsplit.symm
      have hr := hrank blocks.1.flatten blocks.2.2.2.1 lower blocks.2.2.2.2.1
        ((blocks.1.take blockIndex).flatten.length + index + 1) (by
          rw [hdecomp]
          simp only [List.length_append, List.length_tail] at *
          omega)
      have hvalueEq : blocks.1.flatten.getD
          ((blocks.1.take blockIndex).flatten.length + index + 1) 0 =
          (blocks.1.getD blockIndex []).tail.getD index 0 := by
        rw [hdecomp, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
        rw [show (blocks.1.take blockIndex).flatten.length + index + 1 -
          (blocks.1.take blockIndex).flatten.length = index + 1 by omega]
        rw [List.getD_append _ _ _ _ (by simp only [List.length_tail] at hi'; omega)]
        cases hbword : blocks.1.getD blockIndex [] with
        | nil => simp
        | cons first rest => simp
      rw [hvalueEq] at hr
      have hlabelD :
          ((blocks.1.getD blockIndex []).mapIdx (fun position value =>
            value - (0 + (blocks.1.take blockIndex).flatten.length + position + 1))).tail.getD
              index 0 = label := by
        rw [← hb, List.getD_eq_getElem _ _ hi]
        exact hlabelEq
      rw [htail _ _ index hi'] at hlabelD
      simp only [Nat.zero_add] at hlabelD
      omega
  have hupValid (blocks : Target) :
      (up blocks.1).flatten.length = size ∧
      (∀ block ∈ up blocks.1, block ≠ []) ∧
      (up blocks.1).flatten.Pairwise (· < ·) ∧
      (∀ value ∈ (up blocks.1).flatten, lower < value) ∧
      ∀ index < ((up blocks.1).flatMap (fun block => block.rotate 1)).length,
        ((up blocks.1).flatMap (fun block => block.rotate 1)).getD index 0 ≤
          upper + 1 + index := by
    let labels : {labels : List ℕ // labels.length = size ∧ labels.Pairwise (· ≤ ·) ∧
        ∀ label ∈ labels, lower ≤ label ∧ label < upper + 1} :=
      ⟨blocks.1.flatten, blocks.2.1, blocks.2.2.1,
      fun label hlabel =>
        ⟨(blocks.2.2.2.1 label hlabel).1, by
          have := (blocks.2.2.2.1 label hlabel).2; omega⟩⟩
    have hvalues : (up blocks.1).flatten = (equivalence.symm labels).1 := by
      rw [hup]; simpa [up] using hflat (fun index label => label + index + 1) 0 _
    have hne := hnonempty (fun index label => label + index + 1) 0 blocks.1
      blocks.2.2.2.2.1
    refine ⟨?_, hne, ?_, ?_, ?_⟩
    · rw [hvalues]; exact (equivalence.symm labels).2.1
    · rw [hvalues]; exact (equivalence.symm labels).2.2.1
    · rw [hvalues]; exact (equivalence.symm labels).2.2.2.1
    · apply (InversionSeq152Bounds.rotated_suffix_bounds_iff _ _ hne
        (by rw [hvalues]; exact (equivalence.symm labels).2.2.1)).mpr
      refine ⟨?_, ?_⟩
      · rw [hvalues]; exact (equivalence.symm labels).2.2.2.2
      · intro blockIndex hbIndex index hi
        change blockIndex < (up blocks.1).length at hbIndex
        have hbLength : (up blocks.1).length = blocks.1.length := by
          simpa only [List.length_map] using congrArg List.length
            (hshape (fun index label => label + index + 1) 0 blocks.1)
        have hbIndex' : blockIndex < blocks.1.length := by omega
        have hb := hblock (fun index label => label + index + 1) 0 blocks.1 blockIndex
        change (up blocks.1).getD blockIndex [] = _ at hb
        have hi' : index < (blocks.1.getD blockIndex []).tail.length := by
          rw [hb] at hi
          simpa only [List.length_tail, List.length_mapIdx] using hi
        have hsmall := blocks.2.2.2.2.2 (blocks.1.getD blockIndex [])
          (by rw [List.getD_eq_getElem _ _ hbIndex']; exact List.getElem_mem hbIndex')
          ((blocks.1.getD blockIndex []).tail.getD index 0)
          (by rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi')
        have hpre := hprefix (fun index label => label + index + 1) 0
          blocks.1 blockIndex
        rw [hb, htail _ _ index hi']
        simp only [Nat.zero_add]
        omega
  refine ⟨{
    toFun := fun blocks => ⟨down blocks.1, hdownValid blocks⟩
    invFun := fun blocks => ⟨up blocks.1, hupValid blocks⟩
    left_inv := ?_
    right_inv := ?_ }⟩
  · intro blocks
    apply Subtype.ext
    apply hext
    · change (up (down blocks.1)).map List.length = blocks.1.map List.length
      exact (hshape (fun index label => label + index + 1) 0 (down blocks.1)).trans
        (hshape (fun index value => value - (index + 1)) 0 blocks.1)
    · simp only [down, up, hflat, List.mapIdx_mapIdx, Nat.zero_add]
      apply List.ext_getElem
      · simp
      · intro index hleft hright
        have := hrank blocks.1.flatten blocks.2.2.2.1 lower blocks.2.2.2.2.1 index hright
        simp only [List.getElem_mapIdx, Function.comp_apply]
        rw [List.getD_eq_getElem _ _ hright] at this
        omega
  · intro blocks
    apply Subtype.ext
    apply hext
    · change (down (up blocks.1)).map List.length = blocks.1.map List.length
      exact (hshape (fun index value => value - (index + 1)) 0 (up blocks.1)).trans
        (hshape (fun index label => label + index + 1) 0 blocks.1)
    · simp only [down, up, hflat, List.mapIdx_mapIdx, Nat.zero_add]
      apply List.ext_getElem
      · simp
      · intro index hleft hright
        simp only [List.getElem_mapIdx, Function.comp_apply]
        omega

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Labels
