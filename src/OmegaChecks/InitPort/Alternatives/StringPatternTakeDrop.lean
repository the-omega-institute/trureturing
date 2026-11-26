/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import all Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
import all Init.Data.String.Lemmas.Pattern.TakeDrop.Char
import all Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import all Init.Data.String.Lemmas.Pattern.TakeDrop.String
import all Init.Data.String.Slice
import all Init.Data.String.Basic

/-! Search chains for repeated forward and backward prefix matching. -/

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model

open _root_.String.Slice.Pattern.Model

public theorem Pos.skipWhile_eq_iff : type_of% @_root_.String.Slice.Pattern.Model.Pos.skipWhile_eq_iff := by
  intro ρ pat model instancePattern lawful s a b
  fun_induction _root_.String.Slice.Pos.skipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    have h₁ := (_root_.String.Slice.Pattern.Model.Pos.skip?_eq_some_iff).mp h₁
    refine ih.trans ⟨fun ⟨hx, hy⟩ => ⟨.cons _ _ _ h₁ hx, hy⟩, fun ⟨hx, hy⟩ => ⟨?_, hy⟩⟩
    cases hx with
    | nil =>
      refine hy.elim (fun h => (h h₁.matchesAt).elim) (fun h => ?_)
      obtain rfl := h₁.eq h
      exact .nil _
    | cons _ mid _ hx hy' =>
      obtain rfl := hx.eq h₁
      exact hy'
  | case2 pos nextCurr h₁ h₂ =>
    have h₁ := (_root_.String.Slice.Pattern.Model.Pos.skip?_eq_some_iff).mp h₁
    obtain rfl := _root_.String.Slice.Pos.ext (String.Pos.Raw.ext (Nat.le_antisymm h₁.le (Nat.le_of_not_gt h₂)))
    refine ⟨?_, fun ⟨hx, hy⟩ => ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inr h₁⟩
    · exact hx.eq_of_isLongestMatchAt_self h₁
  | case3 pos h =>
    have h := (_root_.String.Slice.Pattern.Model.Pos.skip?_eq_none_iff).mp h
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inl h⟩
    · rintro ⟨(_|⟨_, mid, hx, hy, hz⟩), -⟩
      · rfl
      · exact (h hy.matchesAt).elim

public theorem Pos.skipWhile_eq_self : type_of% @_root_.String.Slice.Pattern.Model.Pos.skipWhile_eq_self := by
  intro ρ pat model instancePattern lawful s pos miss
  have h := (_root_.String.Slice.Pattern.Model.Pos.skip?_eq_none_iff).mpr miss
  rw [_root_.String.Slice.Pos.skipWhile, h]

public theorem Pos.skipWhile_eq_self_iff_or : type_of% @_root_.String.Slice.Pattern.Model.Pos.skipWhile_eq_self_iff_or := by
  intro ρ pat model instancePattern lawful s pos
  exact (Pos.skipWhile_eq_iff pat pos pos).trans ⟨And.right, fun h => ⟨.nil _, h⟩⟩

public theorem Pos.skipWhile_eq_self_iff : type_of% @_root_.String.Slice.Pattern.Model.Pos.skipWhile_eq_self_iff := by
  intro ρ pat model strict instancePattern lawful s pos
  exact Pos.skipWhile_eq_self_iff_or.trans ⟨fun h => h.resolve_right not_isLongestMatchAt_self, Or.inl⟩

public theorem Pos.not_matchesAt_skipWhile : type_of% @_root_.String.Slice.Pattern.Model.Pos.not_matchesAt_skipWhile := by
  intro ρ pat model strict instancePattern lawful s pos
  exact ((_root_.String.Slice.Pattern.Model.Pos.not_matchesAt_or_isLongestMatchAt_skipWhile pat pos)).resolve_right not_isLongestMatchAt_self

public theorem Pos.revSkipWhile_eq_iff : type_of% @_root_.String.Slice.Pattern.Model.Pos.revSkipWhile_eq_iff := by
  intro ρ pat model instancePattern lawful s a b
  fun_induction _root_.String.Slice.Pos.revSkipWhile with
  | case1 pos nextCurr h₁ h₂ ih =>
    have h₁ := (_root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_some_iff).mp h₁
    refine ih.trans ⟨fun ⟨hx, hy⟩ => ⟨.cons _ _ _ hx h₁, hy⟩, fun ⟨hx, hy⟩ => ⟨?_, hy⟩⟩
    cases hx with
    | nil =>
      refine hy.elim (fun h => (h h₁.revMatchesAt).elim) (fun h => ?_)
      obtain rfl := h₁.eq h
      exact .nil _
    | cons mid endP hx' hy' =>
      obtain rfl := hy'.eq h₁
      exact hx'
  | case2 pos nextCurr h₁ h₂ =>
    have h₁ := (_root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_some_iff).mp h₁
    obtain rfl := _root_.String.Slice.Pos.ext (String.Pos.Raw.ext (Nat.le_antisymm h₁.le (Nat.le_of_not_gt h₂)))
    refine ⟨?_, fun ⟨hx, hy⟩ => ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inr h₁⟩
    · exact (hx.eq_of_isLongestRevMatchAt_self h₁).symm
  | case3 pos h =>
    have h := (_root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_none_iff).mp h
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact ⟨.nil _, Or.inl h⟩
    · rintro ⟨(_|⟨mid, endP, hx, hy⟩), -⟩
      · rfl
      · exact (h hy.revMatchesAt).elim

public theorem Pos.revSkipWhile_eq_self : type_of% @_root_.String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self := by
  intro ρ pat model instancePattern lawful s pos miss
  have h := (_root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_none_iff).mpr miss
  rw [_root_.String.Slice.Pos.revSkipWhile, h]

public theorem Pos.revSkipWhile_eq_self_iff_or : type_of% @_root_.String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self_iff_or := by
  intro ρ pat model instancePattern lawful s pos
  exact (Pos.revSkipWhile_eq_iff pat pos pos).trans ⟨And.right, fun h => ⟨.nil _, h⟩⟩

public theorem Pos.revSkipWhile_eq_self_iff : type_of% @_root_.String.Slice.Pattern.Model.Pos.revSkipWhile_eq_self_iff := by
  intro ρ pat model strict instancePattern lawful s pos
  exact Pos.revSkipWhile_eq_self_iff_or.trans ⟨fun h => h.resolve_right not_isLongestRevMatchAt_self, Or.inl⟩

public theorem Pos.not_revMatchesAt_revSkipWhile : type_of% @_root_.String.Slice.Pattern.Model.Pos.not_revMatchesAt_revSkipWhile := by
  intro ρ pat model strict instancePattern lawful s pos
  exact ((_root_.String.Slice.Pattern.Model.Pos.not_revMatchesAt_or_isLongestRevMatchAt_revSkipWhile pat pos)).resolve_right not_isLongestRevMatchAt_self

public theorem startsWith_iff : type_of% @_root_.String.Slice.Pattern.Model.startsWith_iff := by
  intro ρ pat model instancePattern lawful s
  constructor
  · intro yes
    cases eq : s.skipPrefix? pat with
    | none =>
      have no := (_root_.String.Slice.skipPrefix?_eq_none_iff).mp eq
      exact Bool.noConfusion (no.symm.trans yes)
    | some pos =>
      have h := (_root_.String.Slice.Pattern.Model.skipPrefix?_eq_some_iff).mp eq
      exact ⟨⟨pos, _root_.String.Slice.Pattern.Model.isLongestMatchAt_startPos_iff.mpr h⟩⟩
  · intro h
    cases e : s.startsWith pat with
    | true => rfl
    | false => exact ((_root_.String.Slice.Pattern.Model.startsWith_eq_false_iff.mp e) h).elim

public theorem endsWith_iff : type_of% @_root_.String.Slice.Pattern.Model.endsWith_iff := by
  intro ρ pat model instancePattern lawful s
  constructor
  · intro yes
    cases eq : s.skipSuffix? pat with
    | none =>
      have no := (_root_.String.Slice.skipSuffix?_eq_none_iff).mp eq
      exact Bool.noConfusion (no.symm.trans yes)
    | some pos =>
      have h := (_root_.String.Slice.Pattern.Model.skipSuffix?_eq_some_iff).mp eq
      exact ⟨⟨pos, _root_.String.Slice.Pattern.Model.isLongestRevMatchAt_endPos_iff.mpr h⟩⟩
  · intro h
    cases e : s.endsWith pat with
    | true => rfl
    | false => exact ((_root_.String.Slice.Pattern.Model.endsWith_eq_false_iff.mp e) h).elim

private theorem positionBeq {s : String.Slice} (p q : s.Pos) :
    @decide (p = q) (_root_.String.Slice.instDecidableEqPos p q) = true ↔ p = q :=
  ⟨of_decide_eq_true, decide_eq_true⟩

public theorem all_eq_true_iff : type_of% @_root_.String.Slice.Pattern.Model.all_eq_true_iff := by
  intro ρ pat model instancePattern lawful s
  rw [_root_.String.Slice.all_eq_skipPrefixWhile_beq]
  apply (positionBeq _ _).trans
  apply (Pos.skipWhile_eq_iff pat s.startPos s.endPos).trans
  refine ⟨And.left, fun chain => ⟨chain, ?_⟩⟩
  cases eq : s.endPos.skip? pat with
  | none => exact Or.inl (_root_.String.Slice.Pattern.Model.Pos.skip?_eq_none_iff.mp eq)
  | some pos =>
    have found := _root_.String.Slice.Pattern.Model.Pos.skip?_eq_some_iff.mp eq
    have endpoint : pos = s.endPos := (_root_.String.Slice.Pos.endPos_le _).mp found.le
    exact Or.inr (endpoint ▸ found)

public theorem revAll_eq_true_iff : type_of% @_root_.String.Slice.Pattern.Model.revAll_eq_true_iff := by
  intro ρ pat model instancePattern lawful s
  rw [_root_.String.Slice.revAll_eq_skipSuffixWhile_beq]
  apply (positionBeq _ _).trans
  apply (Pos.revSkipWhile_eq_iff pat s.startPos s.endPos).trans
  refine ⟨And.left, fun chain => ⟨chain, ?_⟩⟩
  cases eq : s.startPos.revSkip? pat with
  | none => exact Or.inl (_root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_none_iff.mp eq)
  | some pos =>
    have found := _root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_some_iff.mp eq
    have endpoint : pos = s.startPos := _root_.String.Slice.Pos.ext (String.Pos.Raw.ext
      (Nat.le_antisymm found.le (_root_.String.Slice.Pos.startPos_le _)))
    exact Or.inr (endpoint ▸ found)

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model

namespace OmegaChecks.InitPort.Alternatives.String.Slice

public theorem Pos.skip?_cast : type_of% @_root_.String.Slice.Pos.skip?_cast := by
  intro ρ pat model instancePattern lawful s t eq pos
  apply Option.ext
  intro q
  apply (_root_.String.Slice.Pattern.Model.Pos.skip?_eq_some_iff).trans
  let transport (a b : s.Pos) := @_root_.String.Slice.Pattern.Model.isLongestMatchAt_cast_iff _ pat model s t eq a b
  constructor
  · intro h
    exact Option.map_eq_some_iff.mpr ⟨q.cast eq.symm,
      _root_.String.Slice.Pattern.Model.Pos.skip?_eq_some_iff.mpr ((transport (pos) (q.cast eq.symm)).mp h), rfl⟩
  · intro h
    obtain ⟨b, success, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (transport _ _).mpr (_root_.String.Slice.Pattern.Model.Pos.skip?_eq_some_iff.mp success)

public theorem Pos.skip?_congr : type_of% @_root_.String.Slice.Pos.skip?_congr := by
  intro ρ pat model instancePattern lawful s t eq pos
  exact (Pos.skip?_cast (pat := pat) eq.symm (pos := pos.cast eq))

public theorem Pos.revSkip?_cast : type_of% @_root_.String.Slice.Pos.revSkip?_cast := by
  intro ρ pat model instancePattern lawful s t eq pos
  apply Option.ext
  intro q
  apply (_root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_some_iff).trans
  let transport (a b : s.Pos) := @_root_.String.Slice.Pattern.Model.isLongestRevMatchAt_cast_iff _ pat model s t eq a b
  constructor
  · intro h
    exact Option.map_eq_some_iff.mpr ⟨q.cast eq.symm,
      _root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_some_iff.mpr ((transport (q.cast eq.symm) (pos)).mp h), rfl⟩
  · intro h
    obtain ⟨b, success, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (transport _ _).mpr (_root_.String.Slice.Pattern.Model.Pos.revSkip?_eq_some_iff.mp success)

public theorem Pos.revSkip?_congr : type_of% @_root_.String.Slice.Pos.revSkip?_congr := by
  intro ρ pat model instancePattern lawful s t eq pos
  exact (Pos.revSkip?_cast (pat := pat) eq.symm (pos := pos.cast eq))

end OmegaChecks.InitPort.Alternatives.String.Slice

namespace OmegaChecks.InitPort.Alternatives.String.Slice

private theorem falseOfPositive {b : Bool} {p : Prop} (h : b = true ↔ p) :
    b = false ↔ ¬p := by
  cases b with
  | false => exact ⟨fun _ yes => Bool.noConfusion (h.mpr yes), fun _ => rfl⟩
  | true => exact ⟨(fun eq => nomatch eq), fun no => (no (h.mp rfl)).elim⟩

public theorem endsWith_char_iff_exists_append : type_of% @_root_.String.Slice.endsWith_char_iff_exists_append := by
  intro c s
  apply Pattern.Model.endsWith_iff.trans
  apply _root_.String.Slice.Pattern.Model.Char.revMatchesAt_iff_splits.trans
  constructor
  · rintro ⟨before, after, split⟩
    exact ⟨before, (_root_.String.Slice.splits_endPos_iff.mp split).1.symm⟩
  · rintro ⟨before, eq⟩
    exact ⟨before, "", _root_.String.Slice.splits_endPos_iff.mpr ⟨eq.symm, rfl⟩⟩

public theorem startsWith_slice_eq_false_iff : type_of% @_root_.String.Slice.startsWith_slice_eq_false_iff := by
  intro pat s
  exact falseOfPositive _root_.String.Slice.startsWith_slice_iff

public theorem startsWith_string_eq_false_iff : type_of% @_root_.String.Slice.startsWith_string_eq_false_iff := by
  intro pat s
  exact falseOfPositive _root_.String.Slice.startsWith_string_iff

public theorem startsWith_char_eq_false_iff_forall_append : type_of% @_root_.String.Slice.startsWith_char_eq_false_iff_forall_append := by
  intro c s
  exact (falseOfPositive _root_.String.Slice.startsWith_char_iff_exists_append).trans
    ⟨fun h t eq => h ⟨t, eq⟩, fun h ⟨t, eq⟩ => h t eq⟩

public theorem all_char_iff : type_of% @_root_.String.Slice.all_char_iff := by
  intro pat s
  exact Pattern.Model.all_eq_true_iff.trans
    _root_.String.Slice.Pattern.Model.Char.isLongestMatchAtChain_startPos_endPos_iff_toList

public theorem all_slice_iff : type_of% @_root_.String.Slice.all_slice_iff := by
  intro pat s
  exact Pattern.Model.all_eq_true_iff.trans
    _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestMatchAtChain_startPos_endPos_iff

public theorem endsWith_slice_eq_false_iff : type_of% @_root_.String.Slice.endsWith_slice_eq_false_iff := by
  intro pat s
  exact falseOfPositive _root_.String.Slice.endsWith_slice_iff

public theorem endsWith_string_eq_false_iff : type_of% @_root_.String.Slice.endsWith_string_eq_false_iff := by
  intro pat s
  exact falseOfPositive _root_.String.Slice.endsWith_string_iff

public theorem endsWith_char_eq_false_iff_forall_append : type_of% @_root_.String.Slice.endsWith_char_eq_false_iff_forall_append := by
  intro c s
  exact (falseOfPositive _root_.String.Slice.endsWith_char_iff_exists_append).trans
    ⟨fun h t eq => h ⟨t, eq⟩, fun h ⟨t, eq⟩ => h t eq⟩

public theorem revAll_char_iff : type_of% @_root_.String.Slice.revAll_char_iff := by
  intro pat s
  exact Pattern.Model.revAll_eq_true_iff.trans
    _root_.String.Slice.Pattern.Model.Char.isLongestRevMatchAtChain_startPos_endPos_iff_toList

public theorem revAll_slice_iff : type_of% @_root_.String.Slice.revAll_slice_iff := by
  intro pat s
  exact Pattern.Model.revAll_eq_true_iff.trans
    _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestRevMatchAtChain_startPos_endPos_iff

end OmegaChecks.InitPort.Alternatives.String.Slice

namespace OmegaChecks.InitPort.Alternatives.String

public theorem startsWith_char_eq_false_iff_forall_append : type_of% @_root_.String.startsWith_char_eq_false_iff_forall_append := by
  intro c text
  have h := Slice.startsWith_char_eq_false_iff_forall_append (c := c) (s := text.toSlice)
  rwa [_root_.String.copy_toSlice] at h

public theorem endsWith_char_eq_false_iff_forall_append : type_of% @_root_.String.endsWith_char_eq_false_iff_forall_append := by
  intro c text
  have h := Slice.endsWith_char_eq_false_iff_forall_append (c := c) (s := text.toSlice)
  rwa [_root_.String.copy_toSlice] at h

public theorem Slice.apply_skipSuffixWhile_prop : type_of% @_root_.String.Slice.apply_skipSuffixWhile_prop := by
  intro pred decidable s ne
  exact _root_.String.Slice.Pos.apply_revSkipWhile_prop (pos := s.endPos) (h := ne)

public theorem apply_skipSuffixWhile_prop : type_of% @_root_.String.apply_skipSuffixWhile_prop := by
  intro pred decidable s ne
  exact _root_.String.Pos.apply_revSkipWhile_prop (pos := s.endPos) (h := ne)

public theorem Slice.takeWhile_eq_self_iff : type_of% @_root_.String.Slice.takeWhile_eq_self_iff := by
  intro ρ pat instancePattern s
  exact _root_.String.Slice.sliceTo_eq_self_iff.trans
    (Slice.Pattern.Model.positionBeq (s.skipPrefixWhile pat) s.endPos).symm

public theorem Slice.isEmpty_dropWhile : type_of% @_root_.String.Slice.isEmpty_dropWhile := by
  intro ρ pat instancePattern s
  exact Bool.eq_iff_iff.mpr
    (_root_.String.Slice.isEmpty_dropWhile_iff_takeWhile_eq_self.trans Slice.takeWhile_eq_self_iff)

public theorem Slice.takeWhile_takeWhile : type_of% @_root_.String.Slice.takeWhile_takeWhile := by
  intro ρ pat model instancePattern lawful s
  exact Slice.takeWhile_eq_self_iff.mpr _root_.String.Slice.all_takeWhile

public theorem Slice.takeEndWhile_eq_self_iff : type_of% @_root_.String.Slice.takeEndWhile_eq_self_iff := by
  intro ρ pat instancePattern s
  exact _root_.String.Slice.sliceFrom_eq_self_iff.trans
    (Slice.Pattern.Model.positionBeq (s.skipSuffixWhile pat) s.startPos).symm

public theorem Slice.isEmpty_dropEndWhile : type_of% @_root_.String.Slice.isEmpty_dropEndWhile := by
  intro ρ pat instancePattern s
  exact Bool.eq_iff_iff.mpr
    (_root_.String.Slice.isEmpty_dropEndWhile_iff_takeEndWhile_eq_self.trans Slice.takeEndWhile_eq_self_iff)

public theorem Slice.takeEndWhile_takeEndWhile : type_of% @_root_.String.Slice.takeEndWhile_takeEndWhile := by
  intro ρ pat model instancePattern lawful s
  exact Slice.takeEndWhile_eq_self_iff.mpr _root_.String.Slice.revAll_takeEndWhile

end OmegaChecks.InitPort.Alternatives.String
