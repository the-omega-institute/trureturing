module
public import Init.Data.NeZero
public import OmegaInit.Core
public import OmegaInit.Data.Zero

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (NeZero instNeZeroNatHAdd_1)
end Omega
namespace Omega.NeZero
export _root_.NeZero (casesOn mk ne out rec recOn)
end Omega.NeZero
