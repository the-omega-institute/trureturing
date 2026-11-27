module
public import Init.Data.Option.Basic
public import OmegaInit.Control.Basic

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Option.filterM.match_1 Option.instBEq.beq Option.instBEq.beq.match_1 Option.instDecidableEq.match_1 Option.instDecidableEq.match_3 Option.instDecidableRelLt.match_1 Option.isEqSome.match_1 Option.isSome.match_1 Option.min.match_1 Option.sequence.match_1 instAlternativeOption instFunctorOption instLEOption instLTOption instMonadExceptOfUnitOption instMonadOption liftOption)
end Omega
namespace Omega.Option
export _root_.Option (all all_none all_some any any_none any_some bind bindM bind_none bind_some decidableEqNone decidableNoneEq elim elimM filter filterM get getDM getD_none getD_some getM guard instBEq instDecidableEq instDecidableRelLe instDecidableRelLt instMax instMin instOrElse isEqSome isNone isNone_none isNone_some isSome isSome_none isSome_some join join_none join_some le lt mapA mapM map_none map_some max merge min or orElse orElse_none orElse_some sequence toArray toList tryCatch)
end Omega.Option
