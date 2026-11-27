module
public import OmegaChecks.InitPort.Alternatives.BoolSearch
public import Init.Data.List.Impl
public import Init.Data.List.Sort.Impl
import all Init.Data.List.Control

/-! Pointwise computation of the list implementations at their pinned entry points. -/

namespace OmegaChecks.Interface.Equations

public theorem List.anyM {m : Type → Type u} [Monad m] {α : Type v} (p : α → m Bool) (xs : List α) :
    OmegaChecks.InitPort.Alternatives.List.anyM p xs = _root_.List.anyM p xs := by
  induction xs with
  | nil => exact _root_.List.anyM_nil.symm
  | cons a xs ih =>
    rw [OmegaChecks.InitPort.Alternatives.List.anyM_cons, _root_.List.anyM_cons, ih]

public theorem List.allM {m : Type → Type u} [Monad m] {α : Type v} (p : α → m Bool) (xs : List α) :
    OmegaChecks.InitPort.Alternatives.List.allM p xs = _root_.List.allM p xs := by
  induction xs with
  | nil => exact _root_.List.allM_nil.symm
  | cons a xs ih =>
    rw [OmegaChecks.InitPort.Alternatives.List.allM_cons, _root_.List.allM_cons, ih]

public theorem List.findM? {m : Type → Type u} [Monad m] {α : Type} (p : α → m Bool) (xs : List α) :
    OmegaChecks.InitPort.Alternatives.List.findM? p xs = _root_.List.findM? p xs := by
  induction xs with
  | nil => rw [_root_.List.findM?]; rfl
  | cons a as ih =>
    rw [_root_.List.findM?]
    change (p a >>= fun b => if b then pure (some a) else OmegaChecks.InitPort.Alternatives.List.findM? p as) = _
    rw [ih]
    apply congrArg (fun k => p a >>= k)
    funext b
    cases b <;> rfl

public theorem List.appendTR {α : Type u} (xs ys : List α) :
    _root_.List.append xs ys = _root_.List.appendTR xs ys :=
  congrFun (congrFun (congrFun _root_.List.append_eq_appendTR α) xs) ys

public theorem List.lengthTR {α : Type u} (xs : List α) :
    _root_.List.length xs = _root_.List.lengthTR xs :=
  congrFun (congrFun _root_.List.length_eq_lengthTR α) xs

public theorem List.filterMapTR {α : Type u} {β : Type v} (f : α → Option β) (xs : List α) :
    _root_.List.filterMap f xs = _root_.List.filterMapTR f xs := by
  rw [_root_.List.filterMap_eq_filterMapTR]

public theorem List.mapTR {α : Type u} {β : Type v} (f : α → β) (xs : List α) :
    _root_.List.map f xs = _root_.List.mapTR f xs := by
  rw [_root_.List.map_eq_mapTR]

public theorem List.filterTR {α : Type u} (p : α → Bool) (xs : List α) :
    _root_.List.filter p xs = _root_.List.filterTR p xs := by
  rw [_root_.List.filter_eq_filterTR]

public theorem List.replicateTR {α : Type u} (n : Nat) (a : α) :
    _root_.List.replicate n a = _root_.List.replicateTR n a := by
  rw [_root_.List.replicate_eq_replicateTR]

public theorem List.leftpadTR {α : Type u} (n : Nat) (a : α) (xs : List α) :
    _root_.List.leftpad n a xs = _root_.List.leftpadTR n a xs := by
  rw [_root_.List.leftpad_eq_leftpadTR]

public theorem List.range'TR (start count step : Nat) :
    _root_.List.range' start count step = _root_.List.range'TR start count step := by
  rw [_root_.List.range'_eq_range'TR]

public theorem List.intersperseTR {α : Type u} (separator : α) (xs : List α) :
    _root_.List.intersperse separator xs = _root_.List.intersperseTR separator xs := by
  rw [_root_.List.intersperse_eq_intersperseTR]

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

public theorem List.MergeSort.Internal.mergeTR {α : Type u} (xs ys : List α) (le : α → α → Bool) :
    _root_.List.merge xs ys le = _root_.List.MergeSort.Internal.mergeTR xs ys le := by
  rw [_root_.List.MergeSort.Internal.merge_eq_mergeTR]

public theorem List.MergeSort.Internal.mergeSortTR {α : Type u} (xs : List α) (le : α → α → Bool) :
    _root_.List.mergeSort xs le = _root_.List.MergeSort.Internal.mergeSortTR xs le := by
  rw [_root_.List.MergeSort.Internal.mergeSort_eq_mergeSortTR]

public theorem List.MergeSort.Internal.mergeSortTR₂ {α : Type u} (xs : List α) (le : α → α → Bool) :
    _root_.List.mergeSort xs le = _root_.List.MergeSort.Internal.mergeSortTR₂ xs le := by
  rw [_root_.List.MergeSort.Internal.mergeSort_eq_mergeSortTR₂]

end OmegaChecks.Interface.Equations
