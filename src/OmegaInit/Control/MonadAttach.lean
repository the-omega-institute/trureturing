module
public import Init.Control.MonadAttach
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (MonadAttach)
end Omega
namespace Omega.MonadAttach
export _root_.MonadAttach (CanReturn attach casesOn mk pbind rec recOn trivial)
end Omega.MonadAttach
