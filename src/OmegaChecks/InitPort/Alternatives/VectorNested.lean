module
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

end OmegaChecks.InitPort.Alternatives
