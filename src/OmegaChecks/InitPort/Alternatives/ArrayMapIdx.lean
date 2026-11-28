module
public import Init.Data.Array.MapIdx
public import Init.Data.Vector.MapIdx
import all Init.Data.Array.MapIdx
import all Init.Data.List.MapIdx

/-! Indexed maps preserve array and vector decompositions at the same index. -/
namespace OmegaChecks.InitPort.Alternatives

private theorem sameIndexedLoop [Monad m] (xs : List α) (f : Nat → α → m β) (rest : List α) :
    (fun p : {acc : Array β // rest.length + acc.size = xs.length} => List.mapFinIdxM.go xs
      (fun i a _ => f i a) rest p.val p.property) = (fun p => List.mapIdxM.go f rest p.val) := by
  induction rest with
  | nil => rfl
  | cons a rest ih =>
    exact congrArg (fun tail (p : {acc : Array β // (a :: rest).length + acc.size = xs.length}) =>
      f p.val.size a >>= fun b => tail ⟨p.val.push b, by
        rw [Array.size_push, Nat.add_succ, ← Nat.succ_add]
        exact p.property⟩) ih

public theorem List.mapIdxM_toArray.go : type_of% (private_decl% @_root_.List.mapIdxM_toArray.go) := by
  intro m α β mon xs f rest acc inv
  exact congrFun (sameIndexedLoop xs f rest) ⟨acc, inv⟩

public theorem List.mapIdxM_toArray.go._f : type_of% (private_decl% @_root_.List.mapIdxM_toArray.go._f) := by
  intro m α β mon xs f rest _ acc inv
  exact congrFun (sameIndexedLoop xs f rest) ⟨acc, inv⟩

public theorem Array.mapIdx_append : type_of% @_root_.Array.mapIdx_append := by
  intros
  rw [_root_.Array.mapIdx_eq_mapFinIdx, _root_.Array.mapFinIdx_append,
    _root_.Array.mapIdx_eq_mapFinIdx, _root_.Array.mapIdx_eq_mapFinIdx]

public theorem Array.mapIdx_reverse : type_of% @_root_.Array.mapIdx_reverse := by
  intros
  rw [_root_.Array.mapIdx_eq_mapFinIdx, _root_.Array.mapFinIdx_reverse, _root_.Array.mapIdx_eq_mapFinIdx]

public theorem Array.mem_zipIdx_iff_getElem? : type_of% @_root_.Array.mem_zipIdx_iff_getElem? := by
  intro α x xs
  exact _root_.Array.mk_mem_zipIdx_iff_getElem?

public theorem Vector.mem_zipIdx_iff_getElem? : type_of% @_root_.Vector.mem_zipIdx_iff_getElem? := by
  intros
  exact _root_.Vector.mk_mem_zipIdx_iff_getElem?

public theorem Array.getElem?_mapFinIdx : type_of% @_root_.Array.getElem?_mapFinIdx := by
  intro α β xs f i
  by_cases h : i < xs.size
  · have bound : i < (xs.mapFinIdx f).size :=
      Nat.lt_of_lt_of_eq h _root_.Array.size_mapFinIdx.symm
    rw [getElem?_pos (xs.mapFinIdx f) i bound, _root_.Array.getElem_mapFinIdx, Option.pbind_some' (getElem?_pos xs i h)]
  · have bound : ¬ i < (xs.mapFinIdx f).size := by rwa [_root_.Array.size_mapFinIdx]
    rw [getElem?_neg (xs.mapFinIdx f) i bound, Option.pbind_none' (getElem?_neg xs i h)]

public theorem Vector.getElem?_mapFinIdx : type_of% @_root_.Vector.getElem?_mapFinIdx := by
  intro α n β xs f i
  by_cases h : i < n
  · rw [getElem?_pos (xs.mapFinIdx f) i h, _root_.Vector.getElem_mapFinIdx, Option.pbind_some' (getElem?_pos xs i h)]
  · rw [getElem?_neg (xs.mapFinIdx f) i h, Option.pbind_none' (getElem?_neg xs i h)]

private theorem arraySplit (xs : Array α) (i : Nat) (h : i ≤ xs.size) :
    ∃ (as bs : Array α), xs = as ++ bs ∧ as.size = i := by
  refine ⟨(xs.toList.take i).toArray, (xs.toList.drop i).toArray, ?_, _root_.List.length_take_of_le h⟩
  apply _root_.Array.ext'
  rw [_root_.Array.toList_append]
  exact (_root_.List.take_append_drop ..).symm

public theorem Array.mapFinIdx_eq_append_iff : type_of% @_root_.Array.mapFinIdx_eq_append_iff := by
  intro α β xs f ys zs
  constructor
  · intro eq
    have len := _root_.Array.size_mapFinIdx.symm.trans (congrArg _root_.Array.size eq)
    obtain ⟨as, bs, rfl, width⟩ := arraySplit xs ys.size (by
      rw [len, _root_.Array.size_append]
      exact Nat.le_add_right ..)
    refine ⟨as, bs, rfl, _root_.Array.append_inj (_root_.Array.mapFinIdx_append.symm.trans eq)
      (_root_.Array.size_mapFinIdx.trans width)⟩
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact _root_.Array.mapFinIdx_append

public theorem Array.mapIdx_eq_append_iff : type_of% @_root_.Array.mapIdx_eq_append_iff := by
  intro α β xs f ys zs
  constructor
  · intro eq
    obtain ⟨as, bs, rfl, left, right⟩ :=
      (Array.mapFinIdx_eq_append_iff (xs := xs) (f := fun i a _ => f i a)).mp eq
    exact ⟨as, bs, rfl, left, right⟩
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact Array.mapIdx_append

private theorem indexCongr {bound i j : Nat} (f : (k : Nat) → α → k < bound → β)
    (a : α) (eq : i = j) (hi : i < bound) (hj : j < bound) : f i a hi = f j a hj := by
  cases eq
  rfl

private theorem lastPushIndex (xs : Array α) (a : α) : (xs.push a).size - 1 = xs.size := by
  rw [_root_.Array.size_push, Nat.add_one_sub_one]

public theorem Array.mapFinIdx_eq_push_iff : type_of% @_root_.Array.mapFinIdx_eq_push_iff := by
  intro α β ys xs b f
  constructor
  · intro eq
    have length := _root_.Array.size_mapFinIdx.symm.trans (congrArg _root_.Array.size eq)
    obtain ⟨as, a, rfl⟩ := _root_.Array.exists_push_of_size_eq_add_one (length.trans (_root_.Array.size_push _))
    obtain ⟨last, rest⟩ := _root_.Array.push_eq_push.mp (_root_.Array.mapFinIdx_push.symm.trans eq)
    exact ⟨as, a, rfl, rest, last.symm.trans (indexCongr f a (lastPushIndex as a).symm _ _)⟩
  · rintro ⟨as, a, rfl, rfl, rfl⟩
    exact _root_.Array.mapFinIdx_push.trans
      (congrArg _ (indexCongr f a (lastPushIndex as a).symm _ _))

public theorem Array.mapIdx_eq_push_iff : type_of% @_root_.Array.mapIdx_eq_push_iff := by
  intro α β f ys xs b
  constructor
  · intro eq
    obtain ⟨as, a, rfl, rest, last⟩ :=
      (Array.mapFinIdx_eq_push_iff (xs := xs) (f := fun i a _ => f i a)).mp eq
    exact ⟨a, as, rfl, rest, (congrArg (fun k => f k a) (lastPushIndex as a).symm).trans last.symm⟩
  · rintro ⟨a, as, rfl, rfl, rfl⟩
    exact _root_.Array.mapFinIdx_push

private theorem vectorSplit (xs : Vector α (n + m)) :
    ∃ (as : Vector α n) (bs : Vector α m), xs = as ++ bs := by
  obtain ⟨as, bs, split, width⟩ := arraySplit xs.toArray n
    (xs.size_toArray.symm ▸ Nat.le_add_right n m)
  have both := (congrArg _root_.Array.size split.symm).trans xs.size_toArray
  rw [_root_.Array.size_append, width] at both
  exact ⟨⟨as, width⟩, ⟨bs, Nat.add_left_cancel both⟩, _root_.Vector.toArray_inj.mp split⟩

public theorem Vector.mapFinIdx_eq_append_iff : type_of% @_root_.Vector.mapFinIdx_eq_append_iff := by
  intro α n m β xs f ys zs
  constructor
  · intro eq
    obtain ⟨as, bs, rfl⟩ := vectorSplit xs
    exact ⟨as, bs, rfl, _root_.Vector.append_inj (_root_.Vector.mapFinIdx_append.symm.trans eq)⟩
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact _root_.Vector.mapFinIdx_append

public theorem Vector.mapIdx_eq_append_iff : type_of% @_root_.Vector.mapIdx_eq_append_iff := by
  intro α n m β xs f ys zs
  constructor
  · intro eq
    obtain ⟨as, bs, rfl⟩ := vectorSplit xs
    exact ⟨as, bs, rfl, _root_.Vector.append_inj (_root_.Vector.mapIdx_append.symm.trans eq)⟩
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact _root_.Vector.mapIdx_append

public theorem Vector.mapFinIdx_eq_push_iff : type_of% @_root_.Vector.mapFinIdx_eq_push_iff := by
  intro α n β xs b f ys
  constructor
  · intro eq
    obtain ⟨as, a, rfl⟩ : ∃ (as : _root_.Vector α n) (a : α), xs = as.push a :=
      ⟨_, _, (_root_.Vector.push_pop_back xs).symm⟩
    obtain ⟨last, rest⟩ := _root_.Vector.push_eq_push.mp (_root_.Vector.mapFinIdx_push.symm.trans eq)
    exact ⟨as, a, rfl, rest, last.symm⟩
  · rintro ⟨as, a, rfl, rfl, rfl⟩
    exact _root_.Vector.mapFinIdx_push

public theorem Vector.mapIdx_eq_push_iff : type_of% @_root_.Vector.mapIdx_eq_push_iff := by
  intro α n β f ys xs b
  constructor
  · intro eq
    obtain ⟨as, a, rfl, rest, last⟩ :=
      (Vector.mapFinIdx_eq_push_iff (xs := xs) (f := fun i a _ => f i a)).mp eq
    exact ⟨a, as, rfl, rest, last.symm⟩
  · rintro ⟨a, as, rfl, rfl, rfl⟩
    exact _root_.Vector.mapIdx_push

end OmegaChecks.InitPort.Alternatives
