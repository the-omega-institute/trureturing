module
public import Init.Data.Fin.Basic
public import OmegaInit.Data.Nat.Basic
public import OmegaInit.Data.Nat.Bitwise.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Fin.add.match_1 Fin.elim0.match_1 Fin.modn.eq_1 Fin.modn.match_1 Fin.succ.match_1)
end Omega
namespace Omega.Fin
export _root_.Fin (add addNat cast castAdd castLE castLT castSucc coeToNat coe_neg div elim0 exists_iff instAdd instAndOp instDiv instInhabited instMod instMul instOfNat instOrOp instShiftLeft instShiftRight instSub instXorOp land last lor mod modn modn_lt mul natAdd ne_of_val_ne neg neg_def ofNat pos pred rev shiftLeft shiftRight sub subNat succ toNat toNat_eq_val val_add_one_le_of_gt val_add_one_le_of_lt val_congr val_inj val_le_of_ge val_le_of_le val_lt_of_le val_ne_of_ne val_neg' xor zero_eta)
end Omega.Fin
namespace Omega.Fin.Internal
export _root_.Fin.Internal (ofNat_eq_ofNat)
end Omega.Fin.Internal
