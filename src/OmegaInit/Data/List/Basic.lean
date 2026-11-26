module
public import Init.Data.List.Basic
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (List.modifyHead.eq_1 List.modifyHead.eq_2)
end Omega
namespace Omega.List
export _root_.List (append_assoc head? head?_cons head?_nil headD headD_cons headD_nil isEmpty isEmpty_cons isEmpty_nil modifyHead modifyHead_cons modifyHead_nil reverse reverseAux reverseAux_eq_append reverse_cons singleton tail tail? tail?_cons tail?_nil tailD tailD_cons tailD_nil tail_cons tail_nil)
end Omega.List
