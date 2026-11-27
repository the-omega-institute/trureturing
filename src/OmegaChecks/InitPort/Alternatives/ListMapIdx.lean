module
public import Init.Data.List.MapIdx
import all Init.Data.List.MapIdx

/-! Pointwise proofs for list maps whose callbacks receive an index. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.getElem?_mapIdx : type_of% @_root_.List.getElem?_mapIdx := by
  intro α β f xs i
  by_cases h : i < xs.length
  · have bound : i < (xs.mapIdx f).length := Nat.lt_of_lt_of_eq h _root_.List.length_mapIdx.symm
    rw [_root_.List.getElem?_eq_getElem bound, _root_.List.getElem?_eq_getElem h, _root_.List.getElem_mapIdx]
    rfl
  · have bound : (xs.mapIdx f).length ≤ i := by
      rw [_root_.List.length_mapIdx]
      exact Nat.le_of_not_gt h
    rw [_root_.List.getElem?_eq_none bound, _root_.List.getElem?_eq_none (Nat.le_of_not_gt h)]
    rfl

public theorem List.mapIdx_eq_iff : type_of% @_root_.List.mapIdx_eq_iff := by
  intro α β f ys xs
  constructor
  · intro eq i
    exact eq ▸ List.getElem?_mapIdx
  · intro point
    exact _root_.List.ext_getElem? (fun i => List.getElem?_mapIdx.trans (point i).symm)

public theorem List.mapIdx_cons : type_of% @_root_.List.mapIdx_cons := by
  intros
  rw [_root_.List.mapIdx_eq_mapFinIdx, _root_.List.mapFinIdx_cons, _root_.List.mapIdx_eq_mapFinIdx]

public theorem List.mapIdx_eq_zipIdx_map : type_of% @_root_.List.mapIdx_eq_zipIdx_map := by
  intro α β xs f
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_mapIdx, _root_.List.length_map, _root_.List.length_zipIdx]
  · intros
    rw [_root_.List.getElem_mapIdx, _root_.List.getElem_map, _root_.List.getElem_zipIdx, Nat.zero_add]

public theorem List.mapIdx_eq_nil_iff : type_of% @_root_.List.mapIdx_eq_nil_iff := by
  intro α β f xs
  constructor
  · intro eq
    exact _root_.List.eq_nil_of_length_eq_zero ((_root_.List.length_mapIdx (f := f)).symm.trans
      (congrArg _root_.List.length eq))
  · rintro rfl
    rfl

public theorem List.mapIdx_ne_nil_iff : type_of% @_root_.List.mapIdx_ne_nil_iff := by
  intros
  exact not_congr List.mapIdx_eq_nil_iff

public theorem List.head?_mapIdx : type_of% @_root_.List.head?_mapIdx := by
  intro α β xs f
  cases xs with
  | nil => rfl
  | cons a xs =>
    rw [List.mapIdx_cons]
    rfl

private theorem headOfEq {ys : _root_.List α} {a : α} {as : _root_.List α}
    (eq : ys = a :: as) (h : ys ≠ []) : ys.head h = a := by
  cases eq
  rfl

public theorem List.head_mapIdx : type_of% @_root_.List.head_mapIdx := by
  intro α β xs f nonempty
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons a xs => exact headOfEq List.mapIdx_cons nonempty

public theorem List.mapIdx_mapIdx : type_of% @_root_.List.mapIdx_mapIdx := by
  intro α β γ xs f g
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_mapIdx, _root_.List.length_mapIdx, _root_.List.length_mapIdx]
  · intros
    rw [_root_.List.getElem_mapIdx, _root_.List.getElem_mapIdx, _root_.List.getElem_mapIdx]
    rfl

public theorem List.mapIdx_append : type_of% @_root_.List.mapIdx_append := by
  intros
  rw [_root_.List.mapIdx_eq_mapFinIdx, _root_.List.mapFinIdx_append,
    _root_.List.mapIdx_eq_mapFinIdx, _root_.List.mapIdx_eq_mapFinIdx]

public theorem List.mapIdx_concat : type_of% @_root_.List.mapIdx_concat := by
  intros
  rw [List.mapIdx_append, _root_.List.mapIdx_singleton, Nat.zero_add]

public theorem List.getLast?_mapIdx : type_of% @_root_.List.getLast?_mapIdx := by
  intros
  rw [_root_.List.getLast?_eq_getElem?, _root_.List.length_mapIdx, List.getElem?_mapIdx,
    _root_.List.getLast?_eq_getElem?]

public theorem List.getLast_mapIdx : type_of% @_root_.List.getLast_mapIdx := by
  intro α β l f h
  have eq := List.getLast?_mapIdx (l := l) (f := f)
  rw [_root_.List.getLast?_eq_some_getLast h,
    _root_.List.getLast?_eq_some_getLast (List.mapIdx_ne_nil_iff.mp h)] at eq
  exact Option.some.inj eq

public theorem List.getElem?_mapFinIdx : type_of% @_root_.List.getElem?_mapFinIdx := by
  intro α β l f i
  by_cases h : i < l.length
  · have bound : i < (l.mapFinIdx f).length :=
      Nat.lt_of_lt_of_eq h _root_.List.length_mapFinIdx.symm
    rw [_root_.List.getElem?_eq_getElem bound, _root_.List.getElem_mapFinIdx,
      Option.pbind_some' (_root_.List.getElem?_eq_getElem h)]
  · have bound : (l.mapFinIdx f).length ≤ i := by
      rw [_root_.List.length_mapFinIdx]
      exact Nat.le_of_not_gt h
    rw [_root_.List.getElem?_eq_none bound,
      Option.pbind_none' (_root_.List.getElem?_eq_none (Nat.le_of_not_gt h))]

private theorem splitLength {xs : _root_.List α} {ys zs : _root_.List β}
    (length : xs.length = (ys ++ zs).length) : (xs.take ys.length).length = ys.length := by
  apply _root_.List.length_take_of_le
  rw [length, _root_.List.length_append]
  exact Nat.le_add_right ..

public theorem List.mapFinIdx_eq_append_iff : type_of% @_root_.List.mapFinIdx_eq_append_iff := by
  intro α β ys zs xs f
  constructor
  · intro eq
    have split := (_root_.List.take_append_drop ys.length xs).symm
    have width := splitLength (_root_.List.length_mapFinIdx.symm.trans (congrArg _root_.List.length eq))
    refine ⟨_, _, split, _root_.List.append_inj ?_ (_root_.List.length_mapFinIdx.trans width)⟩
    exact _root_.List.mapFinIdx_append.symm.trans
      ((_root_.List.mapFinIdx_congr split f).symm.trans eq)
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact _root_.List.mapFinIdx_append

public theorem List.mapIdx_eq_append_iff : type_of% @_root_.List.mapIdx_eq_append_iff := by
  intro α β f ys zs xs
  constructor
  · intro eq
    have split := (_root_.List.take_append_drop ys.length xs).symm
    have width := splitLength (_root_.List.length_mapIdx.symm.trans (congrArg _root_.List.length eq))
    refine ⟨_, _, split, _root_.List.append_inj ?_ (_root_.List.length_mapIdx.trans width)⟩
    exact List.mapIdx_append.symm.trans ((congrArg (_root_.List.mapIdx f) split.symm).trans eq)
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact List.mapIdx_append

private theorem mapIdxAccumulator (f : Nat → α → β) (xs : _root_.List α) (acc : Array β) :
    _root_.List.mapIdx.go f xs acc = acc.toList ++ xs.mapIdx (fun i => f (i + acc.size)) := by
  induction xs generalizing acc with
  | nil => exact (_root_.List.append_nil _).symm
  | cons a xs ih =>
    rw [_root_.List.mapIdx.go, ih, Array.toList_push, _root_.List.append_assoc, List.mapIdx_cons,
      _root_.List.singleton_append, Nat.zero_add, Array.size_push]
    apply congrArg (fun tail => acc.toList ++ f acc.size a :: tail)
    apply _root_.List.mapIdx_eq_mapIdx_iff.mpr
    intro i _
    rw [Nat.succ_add, Nat.add_succ]

public theorem List.getElem?_mapIdx_go : type_of% @_root_.List.getElem?_mapIdx_go := by
  intro α β f xs acc i
  rw [mapIdxAccumulator]
  by_cases h : i < acc.size
  · rw [dite_eq_left h, _root_.List.getElem?_append_left (show i < acc.toList.length from h),
      _root_.List.getElem?_eq_getElem (show i < acc.toList.length from h)]
    rfl
  · have bound := Nat.le_of_not_gt h
    rw [dite_eq_right h, _root_.List.getElem?_append_right (show acc.toList.length ≤ i from bound),
      List.getElem?_mapIdx, Array.length_toList, Nat.sub_add_cancel bound]

end OmegaChecks.InitPort.Alternatives
