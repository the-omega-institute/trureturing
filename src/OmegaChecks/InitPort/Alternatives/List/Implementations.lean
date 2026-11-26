module
public import Init.Data.List.Impl
import all Init.Data.List.Impl

/-! Kernel implementations for the equivalent list algorithms. -/

namespace OmegaChecks.InitPort.Alternatives

@[expose] public def List.setTR : type_of% @_root_.List.setTR := @_root_.List.set

public theorem List.set_eq_setTR : @_root_.List.set = @List.setTR := rfl

@[expose] public def List.foldrTR : type_of% @_root_.List.foldrTR := @_root_.List.foldr

public theorem List.foldr_eq_foldrTR : @_root_.List.foldr = @List.foldrTR := rfl

@[expose] public def List.flatMapTR : type_of% @_root_.List.flatMapTR := @_root_.List.flatMap

public theorem List.flatMap_eq_flatMapTR : @_root_.List.flatMap = @List.flatMapTR := rfl

@[expose] public def List.flattenTR : type_of% @_root_.List.flattenTR := @_root_.List.flatten

public theorem List.flatten_eq_flattenTR : @_root_.List.flatten = @List.flattenTR := rfl

@[expose] public def List.takeTR : type_of% @_root_.List.takeTR := @_root_.List.take

public theorem List.take_eq_takeTR : @_root_.List.take = @List.takeTR := rfl

@[expose] public def List.takeWhileTR : type_of% @_root_.List.takeWhileTR := @_root_.List.takeWhile

public theorem List.takeWhile_eq_takeWhileTR : @_root_.List.takeWhile = @List.takeWhileTR := rfl

@[expose] public def List.findRev?TR : type_of% @_root_.List.findRev?TR := @_root_.List.findRev?

public theorem List.findRev?_eq_findRev?TR : @_root_.List.findRev? = @List.findRev?TR := rfl

@[expose] public def List.findSomeRev?TR : type_of% @_root_.List.findSomeRev?TR := @_root_.List.findSomeRev?

public theorem List.findSomeRev?_eq_findSomeRev?TR : @_root_.List.findSomeRev? = @List.findSomeRev?TR := rfl

@[expose] public def List.replaceTR : type_of% @_root_.List.replaceTR := @_root_.List.replace

public theorem List.replace_eq_replaceTR : @_root_.List.replace = @List.replaceTR := rfl

@[expose] public def List.modifyTR : type_of% @_root_.List.modifyTR := @_root_.List.modify

public theorem List.modify_eq_modifyTR : @_root_.List.modify = @List.modifyTR := rfl

@[expose] public def List.insertIdxTR : type_of% @_root_.List.insertIdxTR := @_root_.List.insertIdx

public theorem List.insertIdx_eq_insertIdxTR : @_root_.List.insertIdx = @List.insertIdxTR := rfl

@[expose] public def List.eraseTR : type_of% @_root_.List.eraseTR := @_root_.List.erase

public theorem List.erase_eq_eraseTR : @_root_.List.erase = @List.eraseTR := rfl

@[expose] public def List.erasePTR : type_of% @_root_.List.erasePTR := @_root_.List.eraseP

public theorem List.eraseP_eq_erasePTR : @_root_.List.eraseP = @List.erasePTR := rfl

@[expose] public def List.eraseIdxTR : type_of% @_root_.List.eraseIdxTR := @_root_.List.eraseIdx

public theorem List.eraseIdx_eq_eraseIdxTR : @_root_.List.eraseIdx = @List.eraseIdxTR := rfl

@[expose] public def List.zipWithTR : type_of% @_root_.List.zipWithTR := @_root_.List.zipWith

public theorem List.zipWith_eq_zipWithTR : @_root_.List.zipWith = @List.zipWithTR := rfl

@[expose] public def List.zipIdxTR : type_of% @_root_.List.zipIdxTR := @_root_.List.zipIdx

public theorem List.zipIdx_eq_zipIdxTR : @_root_.List.zipIdx = @List.zipIdxTR := rfl

@[expose] public def List.intercalateTR : type_of% @_root_.List.intercalateTR := @_root_.List.intercalate

public theorem List.intercalate_eq_intercalateTR : @_root_.List.intercalate = @List.intercalateTR := rfl

public theorem List.findRev?_eq_find?_reverse : type_of% @_root_.List.findRev?_eq_find?_reverse := by
  intro α xs p
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findRev?, ih, List.reverse_cons, List.find?_append, List.find?_singleton]
    cases xs.reverse.find? p <;> rfl

public theorem List.findSomeRev?_eq_findSome?_reverse :
    type_of% @_root_.List.findSomeRev?_eq_findSome?_reverse := by
  intro α β xs f
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findSomeRev?, ih, List.reverse_cons, List.findSome?_append, List.findSome?_singleton]
    cases xs.reverse.findSome? f <;> rfl

end OmegaChecks.InitPort.Alternatives
