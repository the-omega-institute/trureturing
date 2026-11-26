module
import all Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Array.Attach

/-! Reconstruct nested vectors from their arrays and the size of each member. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem allMapped {xs : Array α} {f : α → β} {p : β → Prop}
    (h : ∀ x ∈ xs, p (f x)) : ∀ y ∈ xs.map f, p y := by
  intro y mem
  obtain ⟨x, hx, rfl⟩ := _root_.Array.mem_map.mp mem
  exact h x hx

private theorem reconstruct (xs : Array α) (f : α → β)
    (pack : {y // y ∈ xs.map f} → α)
    (roundTrip : ∀ x (h : x ∈ xs), pack ⟨f x, _root_.Array.mem_map_of_mem h⟩ = x) :
    (xs.map f).attach.map pack = xs := by
  apply _root_.Array.ext
  · rw [_root_.Array.size_map, _root_.Array.size_attach, _root_.Array.size_map]
  · intro i hl hr
    rw [_root_.Array.getElem_map]
    apply Eq.trans (congrArg pack (Subtype.ext ?_))
    · exact roundTrip xs[i] (_root_.Array.getElem_mem hr)
    · rw [_root_.Array.getElem_attach]
      exact _root_.Array.getElem_map f _

private theorem rebox {xs : Array (Vector α n)}
    (width : ∀ row ∈ xs.map Vector.toArray, row.size = n) :
    (xs.map Vector.toArray).attach.map (fun ⟨row, h⟩ => Vector.mk row (width row h)) = xs := by
  apply reconstruct
  intro x _
  rfl

public theorem Vector.vector₂_induction : type_of% @_root_.Vector.vector₂_induction := by
  intro α n m P of xss
  obtain ⟨rows, size⟩ := xss
  have width := allMapped (xs := rows) (f := _root_.Vector.toArray)
    (p := fun xs => xs.size = n) (fun v _ => v.size_toArray)
  have given := of _ (_root_.Array.size_map.trans size) width
  refine Eq.mp (congrArg P (_root_.Vector.toArray_inj.mp ?_)) given
  exact rebox width

public theorem Vector.vector₃_induction : type_of% @_root_.Vector.vector₃_induction := by
  intro α n m k P of xss
  obtain ⟨planes, size⟩ := xss
  let unpack (p : _root_.Vector (_root_.Vector α n) m) := p.toArray.map _root_.Vector.toArray
  have height := allMapped (xs := planes) (f := unpack) (p := fun xs => xs.size = m)
    (fun p _ => _root_.Array.size_map.trans p.size_toArray)
  have width := allMapped (xs := planes) (f := unpack)
    (p := fun plane => ∀ row ∈ plane, row.size = n)
    (fun p _ => allMapped (xs := p.toArray) (f := _root_.Vector.toArray)
      (p := fun row => row.size = n) (fun row _ => row.size_toArray))
  have given := of _ (_root_.Array.size_map.trans size) height width
  refine Eq.mp (congrArg P (_root_.Vector.toArray_inj.mp ?_)) given
  apply reconstruct
  intro plane mem
  apply _root_.Vector.toArray_inj.mp
  exact rebox (width _ (_root_.Array.mem_map_of_mem (f := unpack) mem))

public theorem Vector.flatten_append : type_of% @_root_.Vector.flatten_append := by
  intro α n m₁ m₂ xs ys
  apply _root_.Vector.toArray_inj.mp
  change (((xs.toArray ++ ys.toArray).map _root_.Vector.toArray).flatten) = _
  rw [_root_.Array.map_append, _root_.Array.flatten_append]
  rfl

public theorem Vector.append_flatten : type_of% @_root_.Vector.append_flatten := by
  intro α n m₁ m₂ xs ys
  apply _root_.Vector.toArray_inj.mp
  exact (congrArg _root_.Vector.toArray (_root_.Vector.flatten_append (xss₁ := xs) (xss₂ := ys))).symm

public theorem Vector.flatten_push : type_of% @_root_.Vector.flatten_push := by
  intro α n m xs row
  apply _root_.Vector.toArray_inj.mp
  change ((xs.toArray.push row).map _root_.Vector.toArray).flatten = _
  rw [_root_.Array.map_push, _root_.Array.flatten_push]
  rfl

public theorem Vector.map_flatten : type_of% @_root_.Vector.map_flatten := by
  intro α β n m f xs
  apply _root_.Vector.toArray_inj.mp
  change ((xs.toArray.map _root_.Vector.toArray).flatten).map f =
    ((xs.toArray.map (_root_.Vector.map f)).map _root_.Vector.toArray).flatten
  rw [_root_.Array.map_flatten, _root_.Array.map_map, _root_.Array.map_map]
  rfl

public theorem Vector.flatMap_assoc : type_of% @_root_.Vector.flatMap_assoc := by
  intro α n β m γ k xs f g
  apply _root_.Vector.toArray_inj.mp
  apply _root_.Array.flatMap_assoc

public theorem Vector.flatMap_id' : type_of% @_root_.Vector.flatMap_id' := by
  intro α m n xs
  apply _root_.Vector.toArray_inj.mp
  apply _root_.Array.flatMap_def

private theorem rowSizes (xs : _root_.Vector (_root_.Vector α n) m) :
    (xs.toArray.map _root_.Vector.toArray).map _root_.Array.size = _root_.Array.replicate m n := by
  rw [_root_.Array.map_map]
  apply (_root_.Array.map_congr_left (g := fun _ => n) (fun row _ => row.size_toArray)).trans
  exact _root_.Array.map_const'.trans (congrArg (fun k => _root_.Array.replicate k n) xs.size_toArray)

public theorem Vector.eq_iff_flatten_eq : type_of% @_root_.Vector.eq_iff_flatten_eq := by
  intro α n m xs ys
  constructor
  · exact congrArg _root_.Vector.flatten
  · intro eq
    apply _root_.Vector.toArray_inj.mp
    apply (_root_.Array.map_inj_right (fun (x y : _root_.Vector α n) => _root_.Vector.toArray_inj.mp)).mp
    exact _root_.Array.eq_iff_flatten_eq.mpr
      ⟨congrArg _root_.Vector.toArray eq, (rowSizes xs).trans (rowSizes ys).symm⟩

public theorem Vector.flatten_flatten : type_of% @_root_.Vector.flatten_flatten := by
  intro α n m k xs
  apply _root_.Vector.toArray_inj.mp
  change (((xs.toArray.map _root_.Vector.toArray).flatten).map _root_.Vector.toArray).flatten =
    ((xs.toArray.map _root_.Vector.flatten).map _root_.Vector.toArray).flatten
  rw [_root_.Array.map_flatten, _root_.Array.flatten_flatten, _root_.Array.map_map,
    _root_.Array.map_map, _root_.Array.map_map]
  rfl

public theorem Vector.reverse_flatten : type_of% @_root_.Vector.reverse_flatten := by
  intro α m n xs
  apply _root_.Vector.toArray_inj.mp
  change (xs.toArray.map _root_.Vector.toArray).flatten.reverse =
    ((xs.toArray.map _root_.Vector.reverse).reverse.map _root_.Vector.toArray).flatten
  rw [_root_.Array.reverse_flatten, _root_.Array.map_reverse, _root_.Array.map_map, _root_.Array.map_map]
  rfl

public theorem Vector.flatten_reverse : type_of% @_root_.Vector.flatten_reverse := by
  intro α m n xs
  apply _root_.Vector.toArray_inj.mp
  change (xs.toArray.reverse.map _root_.Vector.toArray).flatten =
    ((xs.toArray.map _root_.Vector.reverse).map _root_.Vector.toArray).flatten.reverse
  rw [_root_.Array.map_reverse, _root_.Array.flatten_reverse, _root_.Array.map_map, _root_.Array.map_map]
  rfl

end OmegaChecks.InitPort.Alternatives
