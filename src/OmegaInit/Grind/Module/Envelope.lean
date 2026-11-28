module
public import Init.Grind.Module.Envelope
public import OmegaInit.Grind.Ordered.Module

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Lean.Grind.IntModule.OfNatModule.Q.ind Lean.Grind.IntModule.OfNatModule.Q.liftOn₂ Lean.Grind.IntModule.OfNatModule.Q.mk Lean.Grind.IntModule.OfNatModule.instLEQOfOrderedAdd.match_1 Quot.lift.congr_simp)
end Omega
namespace Omega.Lean.Grind.IntModule.OfNatModule
export _root_.Lean.Grind.IntModule.OfNatModule (Q instAssociativeHAdd instCommutativeHAdd mk_le_mk r r_rfl r_sym r_trans toQ toQ_add toQ_le toQ_lt toQ_smul toQ_zero zero)
end Omega.Lean.Grind.IntModule.OfNatModule
