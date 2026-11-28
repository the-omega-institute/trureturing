module
public import Init.Data.Array.Basic
public import OmegaInit.Data.List.Basic
public import OmegaInit.Control.Id
public import OmegaInit.GetElem
public import OmegaInit.WF

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Array
export _root_.Array (append emptyWithCapacity_eq eraseIdxIfInBounds ext' instAppend map markLinear markLinear_eq mkEmpty_eq propagateMark propagateMark_eq size_eq_length_toList size_push toArray_toList)
end Omega.Array
namespace Omega.List
export _root_.List (size_toArray toList_toArray)
end Omega.List
