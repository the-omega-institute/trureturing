module
public import Init.Data.Order.Classes
public import OmegaInit.Core

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Std
export _root_.Std (IsLinearOrder IsLinearPreorder IsPartialOrder IsPreorder LawfulOrderBEq LawfulOrderInf LawfulOrderLT LawfulOrderLeftLeaningMax LawfulOrderLeftLeaningMin LawfulOrderMax LawfulOrderMin LawfulOrderSup MaxEqOr MinEqOr)
end Omega.Std
namespace Omega.Std.IsLinearOrder
export _root_.Std.IsLinearOrder (casesOn le_total mk rec recOn toIsLinearPreorder toIsPartialOrder)
end Omega.Std.IsLinearOrder
namespace Omega.Std.IsLinearPreorder
export _root_.Std.IsLinearPreorder (casesOn le_total mk rec recOn toIsPreorder)
end Omega.Std.IsLinearPreorder
namespace Omega.Std.IsPartialOrder
export _root_.Std.IsPartialOrder (casesOn le_antisymm mk rec recOn toIsPreorder)
end Omega.Std.IsPartialOrder
namespace Omega.Std.IsPreorder
export _root_.Std.IsPreorder (casesOn le_refl le_trans mk rec recOn)
end Omega.Std.IsPreorder
namespace Omega.Std.LawfulOrderBEq
export _root_.Std.LawfulOrderBEq (beq_iff_le_and_ge casesOn mk rec recOn)
end Omega.Std.LawfulOrderBEq
namespace Omega.Std.LawfulOrderInf
export _root_.Std.LawfulOrderInf (casesOn le_min_iff mk rec recOn)
end Omega.Std.LawfulOrderInf
namespace Omega.Std.LawfulOrderLT
export _root_.Std.LawfulOrderLT (casesOn lt_iff mk rec recOn)
end Omega.Std.LawfulOrderLT
namespace Omega.Std.LawfulOrderLeftLeaningMax
export _root_.Std.LawfulOrderLeftLeaningMax (casesOn max_eq_left max_eq_right mk rec recOn)
end Omega.Std.LawfulOrderLeftLeaningMax
namespace Omega.Std.LawfulOrderLeftLeaningMin
export _root_.Std.LawfulOrderLeftLeaningMin (casesOn min_eq_left min_eq_right mk rec recOn)
end Omega.Std.LawfulOrderLeftLeaningMin
namespace Omega.Std.LawfulOrderMax
export _root_.Std.LawfulOrderMax (casesOn mk rec recOn toLawfulOrderSup toMaxEqOr)
end Omega.Std.LawfulOrderMax
namespace Omega.Std.LawfulOrderMin
export _root_.Std.LawfulOrderMin (casesOn mk rec recOn toLawfulOrderInf toMinEqOr)
end Omega.Std.LawfulOrderMin
namespace Omega.Std.LawfulOrderSup
export _root_.Std.LawfulOrderSup (casesOn max_le_iff mk rec recOn)
end Omega.Std.LawfulOrderSup
namespace Omega.Std.MaxEqOr
export _root_.Std.MaxEqOr (casesOn elim max_eq_or mk rec recOn)
end Omega.Std.MaxEqOr
namespace Omega.Std.MinEqOr
export _root_.Std.MinEqOr (casesOn elim min_eq_or mk rec recOn)
end Omega.Std.MinEqOr
