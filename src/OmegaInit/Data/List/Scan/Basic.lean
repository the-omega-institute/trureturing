module
public import Init.Data.List.Scan.Basic
public import OmegaInit.Control.Id
public import OmegaInit.Data.List.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.List
export _root_.List (scanl scanlM scanr scanrM)
end Omega.List
