module
public import Init.Data.Cast
public import OmegaInit.Coe

public section
namespace Omega
export _root_ (NatCast instNatCastNat instCoeTailNatOfNatCast instCoeHTCTNatOfNatCast)
end Omega
namespace Omega.NatCast
export _root_.NatCast (mk rec recOn casesOn ctorIdx natCast noConfusion noConfusionType mk.noConfusion)
end Omega.NatCast
namespace Omega.Nat
export _root_.Nat (cast)
end Omega.Nat
