module
public import Init.Data.Slice.Basic
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Std
export _root_.Std (Slice)
end Omega.Std
namespace Omega.Std.Slice
export _root_.Std.Slice (casesOn internalRepresentation mk rec recOn)
end Omega.Std.Slice
