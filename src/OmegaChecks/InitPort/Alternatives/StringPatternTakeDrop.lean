/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import all Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
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
