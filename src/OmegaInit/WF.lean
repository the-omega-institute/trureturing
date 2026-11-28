module
public import Init.WF
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Acc WellFounded WellFounded.Nat.fix.go wfParam)
end Omega
namespace Omega.Acc
export _root_.Acc (casesOn intro rec recOn)
end Omega.Acc
namespace Omega.WellFounded
export _root_.WellFounded (casesOn intro rec recOn)
end Omega.WellFounded
namespace Omega.WellFounded.Nat
export _root_.WellFounded.Nat (eager eager_eq fix)
end Omega.WellFounded.Nat
