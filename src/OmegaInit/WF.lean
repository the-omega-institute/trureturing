module
public import Init.WF
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Acc WellFounded WellFoundedRelation WellFounded.Nat.fix.go wfParam)
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
namespace Omega.WellFoundedRelation
export _root_.WellFoundedRelation (casesOn mk rec recOn rel wf)
end Omega.WellFoundedRelation
namespace Omega.Nat
export _root_.Nat (lt_wfRel strongRecOn)
end Omega.Nat
