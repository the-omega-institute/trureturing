module
import all Init.GetElem

/-! Optional indexing fails exactly when its validity predicate fails. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem getElem?_eq_none_iff : type_of% @_root_.getElem?_eq_none_iff := by
  intro cont idx elem dom ge law c i dec
  rw [LawfulGetElem.getElem?_def]
  split
  · next valid => exact ⟨(fun eq => nomatch eq), fun denied => (denied valid).elim⟩
  · next invalid => exact ⟨fun _ => invalid, fun _ => rfl⟩

public theorem none_eq_getElem?_iff : type_of% @_root_.none_eq_getElem?_iff := by
  intro cont idx elem dom ge law c i dec
  exact eq_comm.trans (getElem?_eq_none_iff c i)

public theorem List.none_eq_getElem?_iff : type_of% @_root_.List.none_eq_getElem?_iff := by
  intro α l i
  exact eq_comm.trans _root_.List.getElem?_eq_none_iff

end OmegaChecks.InitPort.Alternatives
