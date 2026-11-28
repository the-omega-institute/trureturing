module
public import Init.While
public import OmegaInit.Classical
public import OmegaInit.Core
public import OmegaInit.SizeOf

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Lean.Loop.forIn.match_1 Lean.Loop.mk.sizeOf_spec repeatM.body repeatM.body.match_1)
end Omega
namespace Omega.Lean
export _root_.Lean (Loop)
end Omega.Lean
namespace Omega.Lean.Loop
export _root_.Lean.Loop (casesOn ctorIdx mk noConfusion noConfusionType rec recOn)
end Omega.Lean.Loop
