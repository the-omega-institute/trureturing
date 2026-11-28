module
public import Init.Data.Slice.Operations
public import OmegaInit.Data.Slice.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Std.Slice.SliceSize.mk.noConfusion)
end Omega
namespace Omega.Std.Slice
export _root_.Std.Slice (SliceSize size)
end Omega.Std.Slice
namespace Omega.Std.Slice.SliceSize
export _root_.Std.Slice.SliceSize (casesOn ctorIdx mk noConfusion noConfusionType rec recOn size)
end Omega.Std.Slice.SliceSize
