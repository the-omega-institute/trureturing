module
public import Init.Data.Range.Polymorphic.UpwardEnumerable
public import OmegaInit.Data.Option.Basic
public import OmegaInit.Data.Nat.Basic

public section
namespace Omega.Std.PRange
export _root_.Std.PRange (UpwardEnumerable InfinitelyUpwardEnumerable LawfulUpwardEnumerable)
export _root_.Std.PRange.UpwardEnumerable (succ? succMany? isSome_succ? succ isSome_succMany? succMany)
end Omega.Std.PRange

namespace Omega.Std.PRange.UpwardEnumerable
export _root_.Std.PRange.UpwardEnumerable (mk succ? succMany? LT isSome_succ? succ isSome_succMany? succMany)
end Omega.Std.PRange.UpwardEnumerable

namespace Omega.Std.PRange.LawfulUpwardEnumerable
export _root_.Std.PRange.LawfulUpwardEnumerable (mk ne_of_lt succMany?_zero succMany?_add_one)
end Omega.Std.PRange.LawfulUpwardEnumerable

namespace Omega.Std.PRange.InfinitelyUpwardEnumerable
export _root_.Std.PRange.InfinitelyUpwardEnumerable (mk isSome_succ?)
end Omega.Std.PRange.InfinitelyUpwardEnumerable
