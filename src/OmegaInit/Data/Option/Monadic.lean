module
public import Init.Data.Option.Monadic
public import OmegaInit.Data.Option.Instances
public import OmegaInit.Data.Option.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Option
export _root_.Option (bindM_none bindM_some filterM_none filterM_some forIn'_none forIn_none forM_eq_forM forM_none forM_some)
end Omega.Option
