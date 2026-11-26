module
public import Init.Data.List.Impl

/-! Pointwise computation of the list implementations at their pinned entry points. -/

namespace OmegaChecks.Interface.Equations

public theorem List.setTR {α : Type u} (xs : List α) (n : Nat) (a : α) :
    _root_.List.set xs n a = _root_.List.setTR xs n a := by
  rw [_root_.List.set_eq_setTR]

public theorem List.foldrTR {α : Type u} {β : Type v} (f : α → β → β) (init : β) (xs : List α) :
    _root_.List.foldr f init xs = _root_.List.foldrTR f init xs := by
  rw [_root_.List.foldr_eq_foldrTR]

public theorem List.flatMapTR {α : Type u} {β : Type v} (f : α → List β) (xs : List α) :
    _root_.List.flatMap f xs = _root_.List.flatMapTR f xs := by
  rw [_root_.List.flatMap_eq_flatMapTR]

public theorem List.flattenTR {α : Type u} (xs : List (List α)) :
    _root_.List.flatten xs = _root_.List.flattenTR xs := by
  rw [_root_.List.flatten_eq_flattenTR]

public theorem List.takeTR {α : Type u} (n : Nat) (xs : List α) :
    _root_.List.take n xs = _root_.List.takeTR n xs := by
  rw [_root_.List.take_eq_takeTR]

public theorem List.takeWhileTR {α : Type u} (p : α → Bool) (xs : List α) :
    _root_.List.takeWhile p xs = _root_.List.takeWhileTR p xs := by
  rw [_root_.List.takeWhile_eq_takeWhileTR]

public theorem List.findRev?TR {α : Type u} (p : α → Bool) (xs : List α) :
    _root_.List.findRev? p xs = _root_.List.findRev?TR p xs := by
  rw [_root_.List.findRev?_eq_findRev?TR]

public theorem List.findSomeRev?TR {α : Type u} {β : Type v} (f : α → Option β) (xs : List α) :
    _root_.List.findSomeRev? f xs = _root_.List.findSomeRev?TR f xs := by
  rw [_root_.List.findSomeRev?_eq_findSomeRev?TR]

public theorem List.replaceTR {α : Type u} [b : BEq α] (xs : List α) (x y : α) :
    _root_.List.replace xs x y = _root_.List.replaceTR xs x y := by
  rw [_root_.List.replace_eq_replaceTR]

public theorem List.modifyTR {α : Type u} (xs : List α) (i : Nat) (f : α → α) :
    _root_.List.modify xs i f = _root_.List.modifyTR xs i f := by
  rw [_root_.List.modify_eq_modifyTR]

public theorem List.insertIdxTR {α : Type u} (xs : List α) (i : Nat) (x : α) :
    _root_.List.insertIdx xs i x = _root_.List.insertIdxTR xs i x := by
  rw [_root_.List.insertIdx_eq_insertIdxTR]

public theorem List.eraseTR {α : Type u} [b : BEq α] (xs : List α) (x : α) :
    _root_.List.erase xs x = _root_.List.eraseTR xs x := by
  rw [_root_.List.erase_eq_eraseTR]

public theorem List.erasePTR {α : Type u} (p : α → Bool) (xs : List α) :
    _root_.List.eraseP p xs = _root_.List.erasePTR p xs := by
  rw [_root_.List.eraseP_eq_erasePTR]

public theorem List.eraseIdxTR {α : Type u} (xs : List α) (i : Nat) :
    _root_.List.eraseIdx xs i = _root_.List.eraseIdxTR xs i := by
  rw [_root_.List.eraseIdx_eq_eraseIdxTR]

public theorem List.zipWithTR {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (xs : List α) (ys : List β) :
    _root_.List.zipWith f xs ys = _root_.List.zipWithTR f xs ys := by
  rw [_root_.List.zipWith_eq_zipWithTR]

public theorem List.zipIdxTR {α : Type u} (xs : List α) (n : Nat) :
    _root_.List.zipIdx xs n = _root_.List.zipIdxTR xs n := by
  rw [_root_.List.zipIdx_eq_zipIdxTR]

public theorem List.intercalateTR {α : Type u} (sep : List α) (xs : List (List α)) :
    _root_.List.intercalate sep xs = _root_.List.intercalateTR sep xs := by
  rw [_root_.List.intercalate_eq_intercalateTR]

end OmegaChecks.Interface.Equations
