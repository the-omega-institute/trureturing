module
import all Init.Data.Vector.Basic
import all Init.Data.Vector.Lemmas
import Init.Data.Array.Lemmas

/-! Transfer folding and predicate evaluation through the underlying fixed-size arrays. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem Vector.foldl_append : type_of% @_root_.Vector.foldl_append := by
  intros
  exact _root_.Array.foldl_append

public theorem Vector.foldr_append : type_of% @_root_.Vector.foldr_append := by
  intros
  exact _root_.Array.foldr_append

public theorem Vector.foldl_reverse : type_of% @_root_.Vector.foldl_reverse := by
  intros
  exact _root_.Array.foldl_reverse

public theorem Vector.foldr_reverse : type_of% @_root_.Vector.foldr_reverse := by
  intros
  exact _root_.Array.foldr_reverse

public theorem Vector.foldl_eq_foldr_reverse : type_of% @_root_.Vector.foldl_eq_foldr_reverse := by
  intros
  exact _root_.Vector.foldr_reverse.symm

public theorem Vector.foldr_eq_foldl_reverse : type_of% @_root_.Vector.foldr_eq_foldl_reverse := by
  intros
  exact _root_.Vector.foldl_reverse.symm

public theorem Vector.any_flatMap : type_of% @_root_.Vector.any_flatMap := by
  intro α n β m xs f p
  exact _root_.Array.any_flatMap (xs := xs.toArray) (f := fun x => (f x).toArray)

public theorem Vector.all_flatMap : type_of% @_root_.Vector.all_flatMap := by
  intro α n β m xs f p
  exact _root_.Array.all_flatMap (xs := xs.toArray) (f := fun x => (f x).toArray)

public theorem Vector.any_flatten : type_of% @_root_.Vector.any_flatten := by
  intro α n m p xs
  unfold _root_.Vector.any _root_.Vector.flatten
  rw [_root_.Array.any_flatten, _root_.Array.any_map]
  rfl

public theorem Vector.all_flatten : type_of% @_root_.Vector.all_flatten := by
  intro α n m p xs
  unfold _root_.Vector.all _root_.Vector.flatten
  rw [_root_.Array.all_flatten, _root_.Array.all_map]
  rfl

public theorem Vector.foldl_flatten : type_of% @_root_.Vector.foldl_flatten := by
  intro β α m n f b xs
  unfold _root_.Vector.foldl _root_.Vector.flatten
  rw [_root_.Array.foldl_flatten, _root_.Array.foldl_map]

public theorem Vector.foldr_flatten : type_of% @_root_.Vector.foldr_flatten := by
  intro α β m n f b xs
  unfold _root_.Vector.foldr _root_.Vector.flatten
  rw [_root_.Array.foldr_flatten, _root_.Array.foldr_map]


public theorem Vector.foldlM_reverse : type_of% @_root_.Vector.foldlM_reverse := by
  intros
  exact Array.foldlM_reverse

public theorem Vector.foldrM_reverse : type_of% @_root_.Vector.foldrM_reverse := by
  intros
  exact Array.foldrM_reverse

public theorem Vector.foldlM_append : type_of% @_root_.Vector.foldlM_append := by
  intros
  exact _root_.Array.foldlM_append

public theorem Vector.foldrM_append : type_of% @_root_.Vector.foldrM_append := by
  intros
  exact _root_.Array.foldrM_append

public theorem Vector.foldlM_push : type_of% @_root_.Vector.foldlM_push := by
  intros
  exact _root_.Array.foldlM_push

public theorem Vector.foldrM_push : type_of% @_root_.Vector.foldrM_push := by
  intros
  exact Array.foldrM_push

end OmegaChecks.InitPort.Alternatives
