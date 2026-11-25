module
public import Init.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (And Bool Eq False Nat Not Or True congrArg rfl)
end Omega
namespace Omega.And
export _root_.And (intro left rec right)
end Omega.And
namespace Omega.Bool
export _root_.Bool (false rec recOn true)
end Omega.Bool
namespace Omega.Eq
export _root_.Eq (rec recOn refl subst symm trans)
end Omega.Eq
namespace Omega.False
export _root_.False (elim rec recOn)
end Omega.False
namespace Omega.Nat
export _root_.Nat (add le le_antisymm le_of_succ_le_succ le_refl le_trans lt mul not_succ_le_zero pred rec recOn sub succ succ_le_succ succ_sub_succ_eq_sub zero zero_le)
end Omega.Nat
namespace Omega.Nat.le
export _root_.Nat.le (refl step)
end Omega.Nat.le
namespace Omega.Or
export _root_.Or (elim inl inr rec)
end Omega.Or
namespace Omega.True
export _root_.True (intro rec recOn)
end Omega.True
