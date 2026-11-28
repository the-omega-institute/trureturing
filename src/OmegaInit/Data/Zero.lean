module
public import Init.Data.Zero
public import OmegaInit.Coe

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (npowRec npowRec.match_1 nsmulRec)
end Omega
namespace Omega.One
export _root_.One (ofOfNat1 toOfNat1)
end Omega.One
namespace Omega.Zero
export _root_.Zero (ofOfNat0 toOfNat0)
end Omega.Zero
