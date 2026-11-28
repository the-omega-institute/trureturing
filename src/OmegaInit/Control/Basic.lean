module
public import Init.Control.Basic
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Alternative ForM ForInStep.value.match_1 MonadControl MonadControlT ToBool control controlAt guard instForInOfForIn' instMonadControlTOfMonadControl instMonadControlTOfPure instOrElseOfAlternative instToBoolBool optional)
export _root_.ForM (forM)
end Omega
namespace Omega.Alternative
export _root_.Alternative (casesOn failure mk orElse rec recOn toApplicative)
end Omega.Alternative
namespace Omega.Bind
export _root_.Bind (bindLeft kleisliLeft kleisliRight)
end Omega.Bind
namespace Omega.ForM
export _root_.ForM (casesOn forM mk rec recOn)
end Omega.ForM
namespace Omega.ForInStep
export _root_.ForInStep (value)
end Omega.ForInStep
namespace Omega.Functor
export _root_.Functor (discard mapRev)
end Omega.Functor
namespace Omega.MonadControl
export _root_.MonadControl (casesOn liftWith mk rec recOn restoreM stM)
end Omega.MonadControl
namespace Omega.MonadControlT
export _root_.MonadControlT (casesOn liftWith mk rec recOn restoreM stM)
end Omega.MonadControlT
namespace Omega.ToBool
export _root_.ToBool (casesOn mk rec recOn toBool)
end Omega.ToBool
