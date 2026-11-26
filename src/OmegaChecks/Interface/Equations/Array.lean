module

public import Init.Data.Array.Lemmas

/-! Pointwise correspondence between the strict list-backed array operations and pinned Init. -/

namespace OmegaChecks.Interface.Equations

public theorem Array.append {α : Type u} (as bs : Array α) :
    _root_.Array.mk (List.append as.toList bs.toList) = _root_.Array.append as bs :=
  _root_.Array.ext' _root_.Array.toList_append.symm

public theorem Array.map {α : Type u} {β : Type v} (f : α → β) (as : Array α) :
    _root_.Array.mk (List.map f as.toList) = _root_.Array.map f as :=
  _root_.Array.ext' _root_.Array.toList_map.symm

end OmegaChecks.Interface.Equations
