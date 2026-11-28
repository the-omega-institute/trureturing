module
public import Init.Data.Int.OfNat
public import OmegaInit.Core
public import OmegaInit.Data.Cast
public import OmegaInit.Data.Int.Basic
public import OmegaInit.Data.Int.DivMod.Basic
public import OmegaInit.Data.Nat.Div.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Int.Nonneg.num_cert.eq_1)
end Omega
namespace Omega.Int.Nonneg
export _root_.Int.Nonneg (add div mod mul natCast num num_cert pow toPoly)
end Omega.Int.Nonneg
namespace Omega.Nat.ToInt
export _root_.Nat.ToInt (add_congr div_congr finVal mod_congr mul_congr natCast_ofNat ofNat_toNat of_diseq of_dvd of_eq of_le of_not_le pow_congr sub_congr toNat_nonneg)
end Omega.Nat.ToInt
