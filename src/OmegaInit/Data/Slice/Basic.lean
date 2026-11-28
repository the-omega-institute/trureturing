module
public import Init.Data.Slice.Basic
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Std.Slice.mk.noConfusion)
end Omega
namespace Omega.Std
export _root_.Std (Slice)
end Omega.Std
namespace Omega.Std.Slice
export _root_.Std.Slice (casesOn ctorIdx internalRepresentation mk noConfusion noConfusionType rec recOn)
end Omega.Std.Slice
