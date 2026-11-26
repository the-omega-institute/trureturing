module
public import Init.Grind.Norm
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Nat.lt.eq_1)
end Omega
namespace Omega.Lean.Grind
export _root_.Lean.Grind (imp_false_eq)
end Omega.Lean.Grind
