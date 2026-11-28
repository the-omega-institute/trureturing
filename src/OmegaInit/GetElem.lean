module
public import Init.GetElem
public import OmegaInit.Data.List.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (GetElem)
end Omega
namespace Omega.Array
export _root_.Array (instGetElemNatLtSize)
end Omega.Array
namespace Omega.GetElem
export _root_.GetElem (casesOn getElem mk rec recOn)
end Omega.GetElem
namespace Omega.List
export _root_.List (getElem_cons_drop instGetElemNatLtLength)
end Omega.List
