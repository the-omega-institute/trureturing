module
import all Init.Data.Vector.Lemmas
import all Init.Data.Vector.Basic
import all Init.Data.Array.Lemmas

/-! Decisions and lookups for vectors retain their size witnesses. -/
namespace OmegaChecks.InitPort.Alternatives

public def Vector.instDecidableExistsVectorZero {α : Type u} (p : _root_.Vector α 0 → Prop)
    [d : Decidable (p #v[])] : Decidable (∃ xs, p xs) :=
  match d with
  | .isTrue h => .isTrue ⟨#v[], h⟩
  | .isFalse h => .isFalse fun ⟨xs, hp⟩ => h (_root_.Vector.eq_empty (xs := xs) ▸ hp)

public theorem Vector.mem_dite_empty_left : type_of% @_root_.Vector.mem_dite_empty_left := by
  intro α p x _ xs
  by_cases h : p
  · rw [dite_eq_left h]
    exact ⟨fun m => (_root_.Vector.not_mem_empty x m).elim, fun ⟨hn, _⟩ => (hn h).elim⟩
  · rw [dite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, fun ⟨_, m⟩ => m⟩

public theorem Vector.mem_ite_empty_left : type_of% @_root_.Vector.mem_ite_empty_left := by
  intro α p x _ xs
  by_cases h : p
  · rw [ite_eq_left h]
    exact ⟨fun m => (_root_.Vector.not_mem_empty x m).elim, fun m => (m.1 h).elim⟩
  · rw [ite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, And.right⟩

public theorem Vector.replicate_beq_replicate : type_of% @_root_.Vector.replicate_beq_replicate := by
  intros
  rw [← _root_.Vector.toArray_beq_toArray, _root_.Vector.toArray_replicate, _root_.Vector.toArray_replicate]
  exact _root_.Array.replicate_beq_replicate

public theorem Vector.getElem?_replace : type_of% @_root_.Vector.getElem?_replace := by
  intro α _ _ n a b xs i
  obtain ⟨data, rfl⟩ := xs
  rw [_root_.Vector.replace_mk, _root_.Vector.getElem?_mk, _root_.Vector.getElem?_mk,
    _root_.Array.getElem?_replace, _root_.Vector.take_mk]
  by_cases h : a ∈ data.take i
  · rw [ite_eq_left h, ite_eq_left (_root_.Vector.mem_mk.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun v => h (_root_.Vector.mem_mk.mp v))]

public theorem Vector.getElem?_replace_of_ne : type_of% @_root_.Vector.getElem?_replace_of_ne := by
  intro α _ _ n a b xs i miss
  rw [_root_.Vector.getElem?_replace]
  exact ite_eq_right (fun h => miss (eq_of_beq h))

public theorem Vector.getElem_replace : type_of% @_root_.Vector.getElem_replace := by
  intro α _ _ n a b xs i hi
  obtain ⟨data, rfl⟩ := xs
  rw [_root_.Vector.getElem_mk, _root_.Vector.take_mk]
  change (data.replace a b)[i]'((_root_.Array.size_replace (xs := data) (a := a) (b := b)).symm ▸ hi) = _
  rw [_root_.Array.getElem_replace hi]
  by_cases h : a ∈ data.take i
  · rw [ite_eq_left h, ite_eq_left (_root_.Vector.mem_mk.mpr h)]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun v => h (_root_.Vector.mem_mk.mp v))]
    rfl

public theorem Vector.replace_push : type_of% @_root_.Vector.replace_push := by
  intro α _ _ n xs a b c
  obtain ⟨data, rfl⟩ := xs
  apply _root_.Vector.toArray_inj.mp
  by_cases h : b ∈ _root_.Vector.mk data rfl
  · rw [ite_eq_left h]
    exact _root_.Array.replace_push.trans (ite_eq_left (_root_.Vector.mem_mk.mp h))
  · rw [ite_eq_right h]
    exact _root_.Array.replace_push.trans (ite_eq_right (fun m => h (_root_.Vector.mem_mk.mpr m)))

end OmegaChecks.InitPort.Alternatives
