module
public import Init.Grind.Module.Basic
public import OmegaInit.Data.Int.DivMod.Basic
public import OmegaInit.Data.Zero

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Lean.Grind.AddCommGroup.mk.noConfusion Lean.Grind.AddCommMonoid.mk.noConfusion Lean.Grind.IntModule.mk.noConfusion Lean.Grind.NatModule.mk.noConfusion)
end Omega
namespace Omega.Lean.Grind
export _root_.Lean.Grind (AddCommGroup AddCommMonoid AddRightCancel IntModule NatModule NoNatZeroDivisors no_nat_zero_divisors)
end Omega.Lean.Grind
namespace Omega.Lean.Grind.AddCommGroup
export _root_.Lean.Grind.AddCommGroup (add_left_inj add_neg_cancel add_right_inj add_sub_cancel casesOn ctorIdx mk neg_add neg_add_cancel neg_eq_iff neg_eq_zero neg_neg neg_sub neg_zero noConfusion noConfusionType rec recOn sub_add_cancel sub_eq_add_neg sub_eq_iff sub_eq_zero_iff sub_self toAddCommMonoid toNeg toSub)
end Omega.Lean.Grind.AddCommGroup
namespace Omega.Lean.Grind.AddCommMonoid
export _root_.Lean.Grind.AddCommMonoid (add_assoc add_comm add_left_comm add_zero casesOn ctorIdx mk noConfusion noConfusionType rec recOn toAdd toZero zero_add)
end Omega.Lean.Grind.AddCommMonoid
namespace Omega.Lean.Grind.AddRightCancel
export _root_.Lean.Grind.AddRightCancel (add_right_cancel casesOn mk rec recOn)
end Omega.Lean.Grind.AddRightCancel
namespace Omega.Lean.Grind.IntModule
export _root_.Lean.Grind.IntModule (add_zsmul casesOn ctorIdx mk mul_zsmul neg_zsmul noConfusion noConfusionType nsmul one_zsmul rec recOn sub_zsmul toAddCommGroup toNatModule zero_zsmul zsmul zsmul_add zsmul_natCast_eq_nsmul zsmul_neg zsmul_sub zsmul_zero)
end Omega.Lean.Grind.IntModule
namespace Omega.Lean.Grind.NatModule
export _root_.Lean.Grind.NatModule (add_nsmul add_one_nsmul casesOn ctorIdx mk mul_nsmul noConfusion noConfusionType nsmul nsmul_add nsmul_zero one_nsmul rec recOn toAddCommMonoid zero_nsmul)
end Omega.Lean.Grind.NatModule
namespace Omega.Lean.Grind.NoNatZeroDivisors
export _root_.Lean.Grind.NoNatZeroDivisors (casesOn eq_zero_of_mul_eq_zero mk mk' no_nat_zero_divisors rec recOn)
end Omega.Lean.Grind.NoNatZeroDivisors
