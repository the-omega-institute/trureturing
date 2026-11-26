module
public import Init.WF

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Acc WellFounded wfParam)
end Omega
namespace Omega.Acc
export _root_.Acc (casesOn intro rec recOn)
end Omega.Acc
namespace Omega.WellFounded
export _root_.WellFounded (casesOn intro rec recOn)
end Omega.WellFounded
