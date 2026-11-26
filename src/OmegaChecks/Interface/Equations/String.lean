module
import all OmegaChecks.Interface.Equations.Collect
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
public import OmegaChecks.InitPort.Alternatives.StringTransforms
import all OmegaChecks.InitPort.Alternatives.StringTransforms
import all Init.Data.String.Iterate
import all Init.Data.String.Extra
import all Init.Data.Iterators.Consumers.Collect
import all Init.Data.Iterators.Consumers.Total
public import Init.Data.String.Lemmas.Iterate
public import Init.Data.String.Lemmas.Pattern.Find.Char
public import Init.Data.String.Lemmas.Pattern.Find.Pred
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Substring
public import OmegaChecks.InitPort.Alternatives.UTF8
import all OmegaChecks.InitPort.Alternatives.UTF8
public import OmegaChecks.InitPort.Alternatives.StringSearch
import all OmegaChecks.InitPort.Alternatives.StringSearch
public import OmegaChecks.InitPort.Alternatives.StringPattern
import all OmegaChecks.InitPort.Alternatives.StringPattern.Searchers
import all Init.Data.String.Pattern.String

/-! Pointwise agreement of finite slice operations with the official iterator operations. -/

namespace OmegaChecks.Interface.Equations

public theorem String.utf8EncodeCharFast (c : Char) :
    OmegaChecks.InitPort.Alternatives.String.utf8EncodeCharFast c = _root_.String.utf8EncodeCharFast c :=
  congrFun _root_.String.utf8EncodeChar_eq_utf8EncodeCharFast c

public theorem String.Slice.Pos.nextFast {s : String.Slice} (pos : s.Pos) (h : pos ≠ s.endPos) :
    OmegaChecks.InitPort.Alternatives.String.Slice.Pos.nextFast pos h = pos.nextFast h :=
  congrFun (congrFun (congrFun _root_.String.Slice.Pos.next_eq_nextFast s) pos) h

public theorem String.Slice.Pattern.instBEqSearchStep.beq {s : String.Slice}
    (a b : _root_.String.Slice.Pattern.SearchStep s) :
    OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.instBEqSearchStep.beq a b =
      _root_.String.Slice.Pattern.instBEqSearchStep.beq a b := by
  have posEq (p q : s.Pos) : (p.offset.byteIdx == q.offset.byteIdx) = (p == q) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq,
      _root_.String.Slice.Pos.ext_iff, _root_.String.Pos.Raw.ext_iff]
  cases a <;> cases b <;>
    simp [OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.instBEqSearchStep.beq,
      _root_.String.Slice.Pattern.instBEqSearchStep.beq, posEq]

public theorem String.Slice.foldl (f : α → Char → α) (init : α) (s : String.Slice) :
    OmegaChecks.InitPort.Alternatives.String.Slice.foldl f init s = s.foldl f init :=
  _root_.String.Slice.foldl_eq_foldl_toList.symm

public theorem String.Slice.foldr (f : Char → α → α) (init : α) (s : String.Slice) :
    OmegaChecks.InitPort.Alternatives.String.Slice.foldr f init s = s.foldr f init :=
  _root_.String.Slice.foldr_eq_foldr_toList.symm

public theorem String.Slice.isNat (s : String.Slice) :
    OmegaChecks.InitPort.Alternatives.String.Slice.isNat s = s.isNat := by
  unfold OmegaChecks.InitPort.Alternatives.String.Slice.isNat _root_.String.Slice.isNat
  simp only [_root_.String.Slice.forIn_eq_forIn_toList (m := Id)]

private theorem firstCharOffset (s : String.Slice) (c : Char) :
    OmegaChecks.InitPort.Alternatives.String.Internal.posOfImpl s.copy c = (s.find c).offset := by
  unfold OmegaChecks.InitPort.Alternatives.String.Internal.posOfImpl _root_.String.Slice.find
  have accepts {xs : List Char} (absent : c ∉ xs) : ∀ x ∈ xs, (x != c) = true := by
    intro x hx
    exact bne_iff_ne.mpr (fun eq => absent (eq ▸ hx))
  cases h : s.find? c with
  | none =>
    have absent : c ∉ s.copy.toList := by
      simpa using (_root_.String.Slice.find?_eq_none_iff c).mp h
    have whole := List.takeWhile_append_of_pos (l₂ := []) (accepts absent)
    simp at whole
    simp [whole]
  | some pos =>
    obtain ⟨t, u, split, absent⟩ := _root_.String.Slice.find?_char_eq_some_iff_splits.mp h
    have eq : s.copy.toList = t.toList ++ c :: u.toList := by
      simpa using congrArg String.toList split.eq_append
    rw [eq, List.takeWhile_append_of_pos (accepts absent)]
    simpa using split.offset_eq_rawEndPos.symm

public theorem String.Internal.posOfImpl (s : String) (c : Char) :
    OmegaChecks.InitPort.Alternatives.String.Internal.posOfImpl s c =
      _root_.String.Internal.posOfImpl s c := by
  simpa [_root_.String.Internal.posOfImpl, _root_.String.find] using firstCharOffset s.toSlice c

public theorem String.Internal.containsImpl (s : String) (c : Char) :
    OmegaChecks.InitPort.Alternatives.String.Internal.containsImpl s c =
      _root_.String.Internal.containsImpl s c :=
  _root_.String.contains_char_eq.symm

public theorem String.Internal.anyImpl (s : String) (p : Char → Bool) :
    OmegaChecks.InitPort.Alternatives.String.Internal.anyImpl s p = _root_.String.Internal.anyImpl s p :=
  _root_.String.contains_bool_eq.symm

public theorem Substring.Raw.posOf (s : Substring.Raw) (c : Char) :
    OmegaChecks.InitPort.Alternatives.Substring.Raw.posOf s c = _root_.Substring.Raw.posOf s c := by
  have mapped : (s.toSlice?.map (fun t => OmegaChecks.InitPort.Alternatives.String.Internal.posOfImpl t.copy c)) =
      s.toSlice?.map (fun t => (t.find c).offset) :=
    Option.map_congr (fun t _ => firstCharOffset t c)
  exact congrArg (fun out : Option String.Pos.Raw => out.getD ⟨s.bsize⟩) mapped

public theorem Substring.Raw.any (s : Substring.Raw) (p : Char → Bool) :
    OmegaChecks.InitPort.Alternatives.Substring.Raw.any s p = _root_.Substring.Raw.any s p :=
  _root_.String.Slice.contains_bool_eq.symm

public theorem String.Slice.PosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad
    {m : Type → Type u} {n : Type v → Type w} {s : String.Slice} [Monad m] [Monad n] :
    @OmegaChecks.InitPort.Alternatives.String.Slice.PosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad m n s _ _ =
      @_root_.String.Slice.PosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad m n s _ _ :=
  finiteIteratorLoop_eq

public theorem String.Slice.RevPosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad
    {m : Type → Type u} {n : Type v → Type w} {s : String.Slice} [Monad m] [Monad n] :
    @OmegaChecks.InitPort.Alternatives.String.Slice.RevPosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad m n s _ _ =
      @_root_.String.Slice.RevPosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad m n s _ _ :=
  finiteIteratorLoop_eq

public theorem String.Slice.ByteIterator.instIteratorLoopUInt8OfMonad
    {m : Type → Type u} {n : Type v → Type w} [Monad m] [Monad n] :
    @OmegaChecks.InitPort.Alternatives.String.Slice.ByteIterator.instIteratorLoopUInt8OfMonad m n _ _ =
      @_root_.String.Slice.ByteIterator.instIteratorLoopUInt8OfMonad m n _ _ :=
  finiteIteratorLoop_eq

public theorem String.Slice.RevByteIterator.instIteratorLoopUInt8OfMonad
    {m : Type → Type u} {n : Type v → Type w} [Monad m] [Monad n] :
    @OmegaChecks.InitPort.Alternatives.String.Slice.RevByteIterator.instIteratorLoopUInt8OfMonad m n _ _ =
      @_root_.String.Slice.RevByteIterator.instIteratorLoopUInt8OfMonad m n _ _ :=
  finiteIteratorLoop_eq

public theorem String.Slice.RevByteIterator.instForInCharOfMonad {m : Type u → Type v} [Monad m] :
    OmegaChecks.InitPort.Alternatives.String.Slice.RevByteIterator.instForInCharOfMonad (m := m) =
      _root_.String.Slice.RevByteIterator.instForInCharOfMonad (m := m) := by
  unfold OmegaChecks.InitPort.Alternatives.String.Slice.RevByteIterator.instForInCharOfMonad
    _root_.String.Slice.RevByteIterator.instForInCharOfMonad
  congr 1
  funext β s b f
  rw [finiteIteratorLoop_eq]

public theorem String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep {s : String.Slice} :
    @OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep s =
      @_root_.String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep s :=
  finiteIteratorLoop_eq

public theorem String.removeLeadingSpaces (s : String) :
    OmegaChecks.InitPort.Alternatives.String.removeLeadingSpaces s = _root_.String.removeLeadingSpaces s := by
  unfold OmegaChecks.InitPort.Alternatives.String.removeLeadingSpaces _root_.String.removeLeadingSpaces
  unfold _root_.String.findLeadingSpacesSize
  let p := fun c : Char => c == '\n'
  let σ := _root_.String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher p
  have loops :
      (fun s : String.Slice => OmegaChecks.InitPort.Alternatives.finiteIteratorLoop (α := σ s) (m := Id) (n := Id)) =
      (fun s => @_root_.String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher.instIteratorLoopIdSearchStep
        _ p s _) := funext (fun _ => finiteIteratorLoop_eq)
  dsimp only
  rw [loops]
  cases (s.startPos.find? p).bind _root_.String.Pos.next? <;> rfl

open _root_.String.Slice.Pattern _root_.String.Slice.Pattern.Model

private theorem finiteListField {α β : Type u} [Std.Iterator α Id β] [Std.Iterators.Finite α Id]
    (it : Std.Iter (α := α) β) : it.ensureTermination.toList = it.toList := rfl

/-- The forward searcher's finite collection yields exactly the pinned model field. -/
public theorem forwardSearcherFiniteField {ρ : Type} (pat : ρ) [PatternModel pat] {σ : String.Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] (s : String.Slice) :
    IsValidSearchFrom pat s.startPos (ToForwardSearcher.toSearcher pat s).ensureTermination.toList =
      IsValidSearchFrom pat s.startPos (ToForwardSearcher.toSearcher pat s).toList :=
  congrArg (IsValidSearchFrom pat s.startPos) (finiteListField _)

/-- The backward searcher's finite collection yields exactly the pinned model field. -/
public theorem backwardSearcherFiniteField {ρ : Type} (pat : ρ) [PatternModel pat] {σ : String.Slice → Type}
    [ToBackwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] (s : String.Slice) :
    IsValidRevSearchFrom pat s.endPos (ToBackwardSearcher.toSearcher pat s).ensureTermination.toList =
      IsValidRevSearchFrom pat s.endPos (ToBackwardSearcher.toSearcher pat s).toList :=
  congrArg (IsValidRevSearchFrom pat s.endPos) (finiteListField _)

end OmegaChecks.Interface.Equations
