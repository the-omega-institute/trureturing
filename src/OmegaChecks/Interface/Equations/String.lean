module
public import Init.Data.String.Lemmas.Iterate
public import Init.Data.String.Lemmas.Pattern.Find.Char
public import Init.Data.String.Lemmas.Pattern.Find.Pred
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.Basic
public import OmegaChecks.InitPort.Alternatives.StringSearch

/-! Pointwise agreement of finite slice operations with the official iterator operations. -/

namespace OmegaChecks.Interface.Equations

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

public theorem String.Internal.posOfImpl (s : String) (c : Char) :
    OmegaChecks.InitPort.Alternatives.String.Internal.posOfImpl s c =
      _root_.String.Internal.posOfImpl s c := by
  unfold OmegaChecks.InitPort.Alternatives.String.Internal.posOfImpl _root_.String.Internal.posOfImpl
    _root_.String.find _root_.String.Slice.find
  have accepts {xs : List Char} (absent : c ∉ xs) : ∀ x ∈ xs, (x != c) = true := by
    intro x hx
    exact bne_iff_ne.mpr (fun eq => absent (eq ▸ hx))
  cases h : s.toSlice.find? c with
  | none =>
    have absent : c ∉ s.toList := by
      simpa using (_root_.String.Slice.find?_eq_none_iff c).mp h
    have whole := List.takeWhile_append_of_pos (l₂ := []) (accepts absent)
    simp at whole
    simp [whole]
  | some pos =>
    obtain ⟨t, u, split, absent⟩ := _root_.String.Slice.find?_char_eq_some_iff_splits.mp h
    have eq : s.toList = t.toList ++ c :: u.toList := by
      simpa using congrArg String.toList split.eq_append
    rw [eq, List.takeWhile_append_of_pos (accepts absent)]
    simpa using split.offset_eq_rawEndPos.symm

public theorem String.Internal.containsImpl (s : String) (c : Char) :
    OmegaChecks.InitPort.Alternatives.String.Internal.containsImpl s c =
      _root_.String.Internal.containsImpl s c :=
  _root_.String.contains_char_eq.symm

public theorem String.Internal.anyImpl (s : String) (p : Char → Bool) :
    OmegaChecks.InitPort.Alternatives.String.Internal.anyImpl s p = _root_.String.Internal.anyImpl s p :=
  _root_.String.contains_bool_eq.symm

end OmegaChecks.Interface.Equations
