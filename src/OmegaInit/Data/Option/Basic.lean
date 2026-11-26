module
public import Init.Data.Option.Basic
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega.Option
export _root_.Option (all all_none all_some any any_none any_some bind bind_none bind_some elim getD_none getD_some isNone isNone_none isNone_some isSome isSome_none isSome_some join join_none join_some le lt map_none map_some merge or orElse orElse_none orElse_some toList tryCatch)
end Omega.Option
