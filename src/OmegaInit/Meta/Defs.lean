module
public import Init.Meta.Defs

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Lean.Meta
export _root_.Lean.Meta (ApplyNewGoals)
end Omega.Lean.Meta
namespace Omega.Lean.Meta.ApplyNewGoals
export _root_.Lean.Meta.ApplyNewGoals (all nonDependentFirst nonDependentOnly rec recOn)
end Omega.Lean.Meta.ApplyNewGoals
