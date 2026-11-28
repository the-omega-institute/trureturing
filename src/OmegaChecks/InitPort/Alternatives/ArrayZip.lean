module
import all Init.Data.Vector.Zip
import all Init.Data.Array.Zip
import Init.Data.Array.Lemmas

/-! The array and vector zip operations inherit their pointwise laws from lists. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem Array.getElem?_zipWith' : type_of% @_root_.Array.getElem?_zipWith' := by
  intro α β γ xs ys f i
  rw [_root_.Array.getElem?_zipWith]
  cases xs[i]? <;> cases ys[i]? <;> rfl

public theorem Array.getElem?_zip_eq_some : type_of% @_root_.Array.getElem?_zip_eq_some := by
  intro α β xs ys z i
  apply (_root_.Array.getElem?_zipWith_eq_some (f := Prod.mk)).trans
  constructor
  · rintro ⟨_, _, hx, hy, rfl⟩
    exact ⟨hx, hy⟩
  · exact fun ⟨hx, hy⟩ => ⟨_, _, hx, hy, rfl⟩

public theorem Array.zipWith_comm_of_comm : type_of% @_root_.Array.zipWith_comm_of_comm := by
  intro α β f comm xs ys
  apply _root_.Array.ext'
  rw [_root_.Array.toList_zipWith, _root_.Array.toList_zipWith]
  exact List.zipWith_comm_of_comm comm

public theorem Array.map_prod_left_eq_zip : type_of% @_root_.Array.map_prod_left_eq_zip := by
  intro α β xs f
  apply _root_.Array.ext'
  rw [_root_.Array.toList_zip, _root_.Array.toList_map, _root_.Array.toList_map]
  exact _root_.List.map_prod_left_eq_zip

public theorem Array.map_prod_right_eq_zip : type_of% @_root_.Array.map_prod_right_eq_zip := by
  intro α β xs f
  apply _root_.Array.ext'
  rw [_root_.Array.toList_zip, _root_.Array.toList_map, _root_.Array.toList_map]
  exact _root_.List.map_prod_right_eq_zip

public theorem Vector.getElem?_zipWith' : type_of% @_root_.Vector.getElem?_zipWith' := by
  intro α β γ n xs ys f i
  rw [_root_.Vector.getElem?_zipWith]
  cases xs[i]? <;> cases ys[i]? <;> rfl

public theorem Vector.getElem?_zip_eq_some : type_of% @_root_.Vector.getElem?_zip_eq_some := by
  intro α n β xs ys z i
  rw [← _root_.Vector.getElem?_toArray, ← _root_.Vector.getElem?_toArray, ← _root_.Vector.getElem?_toArray]
  exact _root_.Array.getElem?_zip_eq_some

public theorem Vector.zipWith_comm_of_comm : type_of% @_root_.Vector.zipWith_comm_of_comm := by
  intro α β n f comm xs ys
  exact _root_.Vector.toArray_inj.mp (_root_.Array.zipWith_comm_of_comm comm)

public theorem Vector.map_prod_left_eq_zip : type_of% @_root_.Vector.map_prod_left_eq_zip := by
  intro α n β xs f
  exact _root_.Vector.toArray_inj.mp _root_.Array.map_prod_left_eq_zip

public theorem Vector.map_prod_right_eq_zip : type_of% @_root_.Vector.map_prod_right_eq_zip := by
  intro α n β xs f
  exact _root_.Vector.toArray_inj.mp _root_.Array.map_prod_right_eq_zip

end OmegaChecks.InitPort.Alternatives
