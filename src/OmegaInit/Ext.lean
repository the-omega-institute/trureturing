module
public import Init.Ext
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Unit.ext)
end Omega
namespace Omega.PUnit
export _root_.PUnit (ext_iff)
end Omega.PUnit
namespace Omega.Thunk
export _root_.Thunk (ext ext_iff)
end Omega.Thunk
