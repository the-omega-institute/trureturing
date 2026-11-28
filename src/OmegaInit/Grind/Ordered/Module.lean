module
public import Init.Grind.Ordered.Module
public import OmegaInit.Data.Order.Classes
public import OmegaInit.Grind.Module.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Lean.Grind
export _root_.Lean.Grind (ExistsAddOfLT OrderedAdd)
end Omega.Lean.Grind
namespace Omega.Lean.Grind.ExistsAddOfLT
export _root_.Lean.Grind.ExistsAddOfLT (casesOn exists_add_of_le mk rec recOn)
end Omega.Lean.Grind.ExistsAddOfLT
namespace Omega.Lean.Grind.OrderedAdd
export _root_.Lean.Grind.OrderedAdd (add_le_add add_le_left add_le_left_iff add_le_right add_le_right_iff casesOn mk rec recOn)
end Omega.Lean.Grind.OrderedAdd
