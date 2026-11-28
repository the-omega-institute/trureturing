module
public import Init.Data.List.Impl
import all Init.Data.List.Impl

/-! Kernel implementations for the equivalent list algorithms. -/

namespace OmegaChecks.InitPort.Alternatives

@[expose] public def List.appendTR : type_of% @_root_.List.appendTR := @_root_.List.append
/- Restoring the public accumulator body also requires a whole-function proof of
`length_eq_lengthTR`. `PublicAlgorithmEquations.ofLength` characterizes that obligation
for every finite prefix and every element type. -/
@[expose] public def List.lengthTR : type_of% @_root_.List.lengthTR := @_root_.List.length

public theorem List.append_eq_appendTR : @_root_.List.append = @List.appendTR := rfl
public theorem List.length_eq_lengthTR : @_root_.List.length = @List.lengthTR := rfl

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.List.lengthTR.eq_1
    {α : Type u} (xs : List α) : List.lengthTR xs = xs.lengthTRAux 0 :=
  _root_.List.length_add_eq_lengthTRAux (n := 0)

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.List.appendTR.eq_1
    {α : Type u} (xs ys : List α) : List.appendTR xs ys = xs.reverse.reverseAux ys := by
  change _root_.List.append xs ys = _root_.List.reverseAux (xs.reverseAux []) ys
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change a :: _root_.List.append xs ys = _root_.List.reverseAux (xs.reverseAux [a]) ys
    rw [_root_.List.reverseAux_reverseAux]
    exact congrArg (a :: ·) ih

@[expose] public def List.filterMapTR : type_of% @_root_.List.filterMapTR := @_root_.List.filterMap

public theorem List.filterMap_eq_filterMapTR : @_root_.List.filterMap = @List.filterMapTR := rfl

public theorem List.filterMap_eq_filterMapTR.go.{v,u} :
    type_of% (private_decl% @_root_.List.filterMap_eq_filterMapTR.go.{v,u}) := by
  intro α β f xs acc
  induction xs generalizing acc with
  | nil => exact (_root_.List.append_nil _).symm
  | cons x xs ih =>
    simp only [_root_.List.filterMapTR.go, _root_.List.filterMap]
    cases result : f x with
    | none => exact ih acc
    | some y =>
      change _root_.List.filterMapTR.go f xs (acc.push y) = acc.toList ++ y :: xs.filterMap f
      rw [ih, _root_.Array.toList_push, _root_.List.append_assoc]
      rfl

@[expose] public def List.mapTR : type_of% @_root_.List.mapTR := @_root_.List.map

public theorem List.map_eq_mapTR : @_root_.List.map = @List.mapTR := rfl

@[expose] public def List.filterTR : type_of% @_root_.List.filterTR := @_root_.List.filter

public theorem List.filter_eq_filterTR : @_root_.List.filter = @List.filterTR := rfl

@[expose] public def List.replicateTR : type_of% @_root_.List.replicateTR := @_root_.List.replicate

public theorem List.replicate_eq_replicateTR : @_root_.List.replicate = @List.replicateTR := rfl

@[expose] public def List.leftpadTR : type_of% @_root_.List.leftpadTR := @_root_.List.leftpad

public theorem List.leftpad_eq_leftpadTR : @_root_.List.leftpad = @List.leftpadTR := rfl

@[expose] public def List.range'TR : type_of% @_root_.List.range'TR := @_root_.List.range'

public theorem List.range'_eq_range'TR : @_root_.List.range' = @List.range'TR := rfl

@[expose] public def List.intersperseTR : type_of% @_root_.List.intersperseTR := @_root_.List.intersperse

public theorem List.intersperse_eq_intersperseTR : @_root_.List.intersperse = @List.intersperseTR := rfl


public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.List.mapTR.eq_1 {α : Type u} {β : Type v} (f : α → β) (xs : List α) :
    List.mapTR f xs = _root_.List.mapTR.loop f xs [] := (_root_.List.mapTR_loop_eq (bs := []) (as := xs) (f := f)).symm

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.List.filterTR.eq_1 {α : Type u} (p : α → Bool) (xs : List α) :
    List.filterTR p xs = _root_.List.filterTR.loop p xs [] := (_root_.List.filterTR_loop_eq (bs := []) (as := xs) (p := p)).symm

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.List.leftpadTR.eq_1 {α : Type u} (n : Nat) (a : α) (xs : List α) :
    List.leftpadTR n a xs = _root_.List.replicateTR.loop a (n - xs.length) xs :=
  (_root_.List.replicateTR_loop_eq _).symm

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.List.intersperseTR.eq_3 {α : Type u} (sep x y : α) (xs : List α) :
    List.intersperseTR sep (x :: y :: xs) = x :: sep :: y :: xs.foldr (fun a r => sep :: a :: r) [] := by
  change _root_.List.intersperse sep (x :: y :: xs) = _
  rw [_root_.List.intersperse] <;> try (intro h; cases h)
  apply congrArg (fun l => x :: sep :: l)
  induction xs generalizing y with
  | nil => rfl
  | cons z zs ih => exact congrArg (fun l => y :: sep :: l) (ih z)

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
