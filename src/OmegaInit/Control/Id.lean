module
public import Init.Control.Id
public import OmegaInit.Control.MonadAttach

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Id Id.hasBind Id.instMonad Id.instMonadAttach Id.instMonadLiftTOfPure Id.instOfNat Id.run)
end Omega
namespace Omega.ForIn
export _root_.ForIn (toArray toList)
end Omega.ForIn
