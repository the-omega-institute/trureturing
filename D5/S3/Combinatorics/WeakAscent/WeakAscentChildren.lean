/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentChildren
   mirror-E: none(waiver:weak-ascent-succession)
   anchors: []
   utility: none
   digest: Admitted letters correspond bijectively to the common generating-tree children. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentStates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentChildren

open WeakAscentDefs WeakAscentGrowth WeakAscentStates

noncomputable def weakLabel (e : List ℕ) : ℕ × ℕ :=
  if e.getLast?.getD 0 = e.foldr max 0 then
    (e.foldr max 0 - inversionBottom e + 1, 1 + wasc e - e.foldr max 0)
  else (e.foldr max 0 - inversionBottom e, 1 + wasc e - e.foldr max 0 + 1)

def childLabel (height slack : ℕ) : Fin height ⊕ Fin slack → ℕ × ℕ
  | .inl index => (index.val + 1, slack + 1)
  | .inr index => (height + slack - index.val, index.val + 1)

theorem weak_children_rule (e : List ℕ) (hempty : e ≠ [])
    (he : IsWeakAscent e) (havoid : ¬ Contains210 e) :
    0 < (weakLabel e).1 ∧ 0 < (weakLabel e).2 ∧
    ∃ correspondence :
      {letter : ℕ // inversionBottom e ≤ letter ∧ letter ≤ 1 + wasc e} ≃
        (Fin (weakLabel e).1 ⊕ Fin (weakLabel e).2),
      ∀ letter, weakLabel (e ++ [letter.val]) =
        childLabel (weakLabel e).1 (weakLabel e).2 (correspondence letter) := by
  classical
  let maximum := e.foldr max 0
  let bottom := inversionBottom e
  let bound := 1 + wasc e
  let last := e.getLast?.getD 0
  let height := (weakLabel e).1
  let slack := (weakLabel e).2
  have hmax : maximum < bound := height_dominates e he
  obtain ⟨hbottom, hlast, hextreme⟩ := last_extreme e hempty havoid
  change bottom ≤ maximum at hbottom
  change bottom ≤ last at hlast
  change last = maximum ∨ last = bottom ∧ bottom < maximum at hextreme
  have hlabel :
      (height = maximum - bottom + 1 ∧ slack = bound - maximum ∧ last = maximum) ∨
      (height = maximum - bottom ∧ slack = bound - maximum + 1 ∧
        last = bottom ∧ bottom < maximum) := by
    rcases hextreme with hright | ⟨hleft, hstrict⟩
    · left
      simp only [height, slack, weakLabel, show e.getLast?.getD 0 = e.foldr max 0
        from hright, if_true]
      exact ⟨rfl, rfl, hright⟩
    · right
      have hnot : e.getLast?.getD 0 ≠ e.foldr max 0 := by
        change last ≠ maximum
        omega
      simp only [height, slack, weakLabel, hnot, if_false]
      exact ⟨rfl, rfl, hleft, hstrict⟩
  have hheight : 0 < height := by rcases hlabel with hright | hleft <;> omega
  have hslack : 0 < slack := by rcases hlabel with hright | hleft <;> omega
  let encode : {letter : ℕ // bottom ≤ letter ∧ letter ≤ bound} →
      Fin height ⊕ Fin slack := fun letter =>
    if hlower : letter.val < maximum then
      .inl ⟨maximum - letter.val - 1, by
        have := letter.property
        rcases hlabel with hright | hleft <;> omega⟩
    else if hmiddle : last = maximum ∧ letter.val = maximum then
      .inl ⟨maximum - bottom, by
        rcases hlabel with hright | hleft <;> omega⟩
    else .inr ⟨bound - letter.val, by
      have := letter.property
      rcases hlabel with hright | hleft <;> omega⟩
  let decode : Fin height ⊕ Fin slack →
      {letter : ℕ // bottom ≤ letter ∧ letter ≤ bound}
    | .inl index =>
      if hmiddle : last = maximum ∧ index.val = maximum - bottom then
        ⟨maximum, by omega⟩
      else ⟨maximum - 1 - index.val, by
        have := index.isLt
        rcases hlabel with hright | hleft <;> omega⟩
    | .inr index => ⟨bound - index.val, by
      have := index.isLt
      rcases hlabel with hright | hleft <;> omega⟩
  have left_inverse : Function.LeftInverse decode encode := by
    intro letter
    apply Subtype.ext
    have := letter.property
    dsimp only [encode]
    split_ifs with hlower hmiddle
    · dsimp only [decode]
      split_ifs with hindex
      · omega
      · dsimp only
        omega
    · dsimp only [decode]
      rw [dif_pos ⟨hmiddle.1, rfl⟩]
      exact hmiddle.2.symm
    · dsimp only [decode]
      omega
  have right_inverse : Function.RightInverse decode encode := by
    intro index
    cases index with
    | inl index =>
      have hindex := index.isLt
      dsimp only [decode]
      split_ifs with hmiddle
      · dsimp only [encode]
        rw [dif_neg (Nat.lt_irrefl maximum), dif_pos ⟨hmiddle.1, rfl⟩]
        congr 1
        apply Fin.ext
        exact hmiddle.2.symm
      · have hlower : maximum - 1 - index.val < maximum := by
          rcases hlabel with hright | hleft <;> omega
        dsimp only [encode]
        rw [dif_pos hlower]
        congr 1
        apply Fin.ext
        dsimp only
        rcases hlabel with hright | hleft <;> omega
    | inr index =>
      have hindex := index.isLt
      have hlower : ¬ bound - index.val < maximum := by
        rcases hlabel with hright | hleft <;> omega
      have hmiddle : ¬ (last = maximum ∧ bound - index.val = maximum) := by
        rcases hlabel with hright | hleft <;> omega
      dsimp only [decode, encode]
      rw [dif_neg hlower, dif_neg hmiddle]
      congr 1
      apply Fin.ext
      dsimp only
      rcases hlabel with hright | hleft <;> omega
  let correspondence : {letter : ℕ // bottom ≤ letter ∧ letter ≤ bound} ≃
      (Fin height ⊕ Fin slack) :=
    ⟨encode, decode, left_inverse, right_inverse⟩
  refine ⟨hheight, hslack, correspondence, ?_⟩
  intro letter
  have hletter := letter.property
  obtain ⟨hchildmax, hchildasc, hchildbottom⟩ := append_state e letter.val
  have hchildlast : (e ++ [letter.val]).getLast?.getD 0 = letter.val := by
    simp [List.getLast?_append]
  change (e ++ [letter.val]).foldr max 0 = max maximum letter.val at hchildmax
  change wasc (e ++ [letter.val]) = wasc e +
    (if e = [] then 0 else if last ≤ letter.val then 1 else 0) at hchildasc
  change inversionBottom (e ++ [letter.val]) =
    (if letter.val < maximum then max bottom letter.val else bottom) at hchildbottom
  have hmaxletter : max bottom letter.val = letter.val := max_eq_right hletter.1
  by_cases hlower : letter.val < maximum
  · have hnewmax : (e ++ [letter.val]).foldr max 0 = maximum := by
      rw [hchildmax, max_eq_left (Nat.le_of_lt hlower)]
    have hnewbottom : inversionBottom (e ++ [letter.val]) = letter.val := by
      rw [hchildbottom, if_pos hlower, hmaxletter]
    have hnewlast : (e ++ [letter.val]).getLast?.getD 0 ≠
        (e ++ [letter.val]).foldr max 0 := by rw [hchildlast, hnewmax]; omega
    change weakLabel (e ++ [letter.val]) = childLabel height slack (encode letter)
    dsimp only [encode]
    rw [dif_pos hlower, weakLabel, if_neg hnewlast, hnewmax, hnewbottom]
    dsimp only [childLabel]
    apply Prod.ext
    · omega
    · rcases hlabel with ⟨hh, hk, ha⟩ | ⟨hh, hk, ha, hd⟩
      · have hnot : ¬ last ≤ letter.val := by omega
        rw [hchildasc, if_neg hempty, if_neg hnot]
        omega
      · have hyes : last ≤ letter.val := by omega
        rw [hchildasc, if_neg hempty, if_pos hyes]
        omega
  · have hnewmax : (e ++ [letter.val]).foldr max 0 = letter.val := by
      rw [hchildmax, max_eq_right (by omega)]
    have hnewbottom : inversionBottom (e ++ [letter.val]) = bottom := by
      rw [hchildbottom, if_neg hlower]
    have hnewlast : (e ++ [letter.val]).getLast?.getD 0 =
        (e ++ [letter.val]).foldr max 0 := hchildlast.trans hnewmax.symm
    have hyes : last ≤ letter.val := by
      rcases hextreme with ha | ⟨ha, hd⟩ <;> omega
    have hnewasc : wasc (e ++ [letter.val]) = wasc e + 1 := by
      rw [hchildasc, if_neg hempty, if_pos hyes]
    change weakLabel (e ++ [letter.val]) = childLabel height slack (encode letter)
    dsimp only [encode]
    rw [dif_neg hlower]
    split_ifs with hmiddle
    · rw [weakLabel, if_pos hnewlast, hnewmax, hnewbottom, hnewasc]
      dsimp only [childLabel]
      apply Prod.ext
      · omega
      · rcases hlabel with hright | hleft <;> omega
    · rw [weakLabel, if_pos hnewlast, hnewmax, hnewbottom, hnewasc]
      dsimp only [childLabel]
      apply Prod.ext <;> rcases hlabel with hright | hleft <;> omega

end D5.S3.Combinatorics.WeakAscent.WeakAscentChildren
