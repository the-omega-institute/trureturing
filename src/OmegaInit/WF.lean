module
public import Init.WF
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Acc WellFounded WellFounded.Nat.fix.go wfParam)
end Omega
namespace Omega.Acc
export _root_.Acc (casesOn intro inv ndrec ndrecOn rec recOn)
end Omega.Acc
namespace Omega.WellFounded
export _root_.WellFounded (apply casesOn fix fixF fixF_eq fix_eq induction intro rec recOn recursion val_wrap wrap)
end Omega.WellFounded
namespace Omega.WellFounded.Nat
export _root_.WellFounded.Nat (eager eager_eq fix)
end Omega.WellFounded.Nat
