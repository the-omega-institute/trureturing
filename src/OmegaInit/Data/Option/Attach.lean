module
public import Init.Data.Option.Attach
public import OmegaInit.Data.Option.Lemmas

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (
  Option.attachWith.congr_simp Option.attachWith.match_1 Option.unattach.eq_1)
end Omega

namespace Omega.Option
export _root_.Option (
  attach attachWith attachWith_map_subtype_val attachWith_none attach_map_subtype_val
  attach_map_val attach_none attach_some isNone_attach isNone_attachWith isNone_unattach
  isSome_attach isSome_attachWith isSome_unattach unattach unattach_attach unattach_attachWith
  unattach_none unattach_some)
end Omega.Option
