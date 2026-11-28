module
public import Init.Data.Array.Bootstrap
public import OmegaInit.Data.Array.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Array
export _root_.Array (append_assoc append_empty append_eq_append empty_append toList_append toList_empty toList_push)
end Omega.Array
