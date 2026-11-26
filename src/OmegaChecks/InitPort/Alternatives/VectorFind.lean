module
import all OmegaChecks.InitPort.Alternatives.ArrayFind
public import Init.Data.Vector.Find

/-! Search on vectors through their underlying arrays. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem Vector.find?_replicate_eq_none_iff : type_of% @_root_.Vector.find?_replicate_eq_none_iff := by
  intros
  rw [Vector.replicate_eq_mk_replicate, Vector.find?_mk]
  exact _root_.Array.find?_replicate_eq_none_iff

public theorem Vector.find?_flatMap : type_of% @_root_.Vector.find?_flatMap := by
  intro α n β m xs f p
  exact _root_.Array.find?_flatMap (xs := xs.toArray) (f := fun x => (f x).toArray)

public theorem Vector.find?_flatten : type_of% @_root_.Vector.find?_flatten := by
  intro α m n xs p
  change (xs.toArray.map _root_.Vector.toArray).flatten.find? p = _
  rw [Array.find?_flatten, Array.findSome?_map]
  rfl

public theorem Vector.getElem?_zero_flatten : type_of% @_root_.Vector.getElem?_zero_flatten := by
  intro α m n xs
  rw [← Vector.getElem?_toArray]
  change (xs.toArray.map _root_.Vector.toArray).flatten[0]? = _
  rw [Array.getElem?_zero_flatten, Array.findSome?_map]
  rw [← Vector.findSome?_toArray, ← Array.findSome?_toList, ← Array.findSome?_toList]
  apply findSomePointwise
  exact fun v => _root_.Vector.getElem?_toArray (xs := v)

public theorem Vector.getElem_zero_flatten.proof : type_of% @_root_.Vector.getElem_zero_flatten.proof := by
  intros
  rw [← _root_.Vector.getElem?_zero_flatten, _root_.Vector.getElem?_eq_getElem ‹_›]
  rfl

public theorem Vector.getElem_zero_flatten : type_of% @_root_.Vector.getElem_zero_flatten := by
  intros
  apply Option.some.inj
  exact (_root_.Vector.getElem?_eq_getElem ‹_›).symm.trans ((_root_.Vector.getElem?_zero_flatten).trans (Option.some_get _).symm)

public theorem Vector.find?_flatten_eq_none_iff : type_of% @_root_.Vector.find?_flatten_eq_none_iff := by
  intros
  rw [_root_.Vector.find?_flatten, _root_.Vector.findSome?_eq_none_iff]
  exact ⟨fun h a m y hy => flipped.mpr (_root_.Vector.find?_eq_none.mp (h a m) y hy),
    fun h a m => _root_.Vector.find?_eq_none.mpr (fun y hy => flipped.mp (h a m y hy))⟩

public theorem Vector.find?_flatMap_eq_none_iff : type_of% @_root_.Vector.find?_flatMap_eq_none_iff := by
  intros
  rw [_root_.Vector.find?_flatMap, _root_.Vector.findSome?_eq_none_iff]
  exact ⟨fun h a m y hy => flipped.mpr (_root_.Vector.find?_eq_none.mp (h a m) y hy),
    fun h a m => _root_.Vector.find?_eq_none.mpr (fun y hy => flipped.mp (h a m y hy))⟩

public theorem Vector.findFinIdx?_eq_bind_find?_finIdxOf? : type_of% @_root_.Vector.findFinIdx?_eq_bind_find?_finIdxOf? := by
  intro α _ _ n xs p
  rcases xs with ⟨xs, rfl⟩
  simp only [Vector.findFinIdx?, Vector.find?, Vector.finIdxOf?, Array.findFinIdx?_eq_bind_find?_finIdxOf?]
  cases xs.find? p <;> rfl

public theorem Vector.findFinIdx?_push : type_of% @_root_.Vector.findFinIdx?_push := by
  intro α n xs a p
  rcases xs with ⟨xs, rfl⟩
  simp only [Vector.findFinIdx?, Vector.toArray_push, Array.findFinIdx?_push]
  cases xs.findFinIdx? p <;> cases p a <;> rfl

public theorem Vector.findFinIdx?_append : type_of% @_root_.Vector.findFinIdx?_append := by
  intro α n m xs ys p
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [Vector.findFinIdx?, Vector.toArray_append, Array.findFinIdx?_append]
  cases xs.findFinIdx? p <;> cases ys.findFinIdx? p <;> rfl

end OmegaChecks.InitPort.Alternatives
